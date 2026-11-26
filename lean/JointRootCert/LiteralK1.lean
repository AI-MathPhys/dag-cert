/-
Joint Root Certification: `prop:representation-coupling` (Trajectory Coupling Across
Circuit Representations), stated over DAG circuits with sharing and with the retirement
clause proved rather than assumed.

Manuscript result covered:

* `prop:representation-coupling`.  Both sentences, in the DAG model `CostEngines.Dag`
  (gates may be shared by several parents):

  1. *Congruence of the three transformations at arbitrary (inner or root) gates.*
     `bypass_move` (unary bypass), `intern_move` (interning of gates with identical child
     sets) and `dyadic_move` (replacement of a child list by gates whose terminal supports
     cover the same terminals) each leave the heap maximum of the rewritten child list
     unchanged for every exact valuation; `refines_of_local` turns any family of such local
     rewrites into `Refines G G'`; `eager_refines` shows that the eager engines on `G` and
     `G'` then store the same interval at every gate at every time.  `exact_eq_sup` is the
     underlying fact that a gate computes the maximum over its terminal support.

  2. *Strict-dominance retirement.*  `selImpl` is the Graph-Selective engine of
     `RetireFinal.lean` (retirement of incidences `(v, c)` with `u(c) < l(v)` chosen by any
     candidate policy, reference-counted release of orphaned gates, root-action retirement
     at queries) packaged as an `OracleImpl` driven by observations; `eagImpl` is the
     full-incidence engine.  `sel_answer_eq` proves that the two expose the same
     leader-and-stop oracle on EVERY history, and `retirement_coupling_literal` concludes
     identical histories, replies and stopping times for every controller, reward tape and
     controller tape.  No hypothesis about the run is made: nestedness of the terminal
     boxes is derived from the running-intersection construction `boxStep`.
     `representation_coupling_literal` composes 1 and 2: the Graph-Selective engine on a
     transformed circuit is coupled with the Graph-Eager engine on the original circuit.
     `interval_coupling_literal` is the numerical version (all root intervals) for the
     engine with protected roots.  `selective_run_facts` records that a gate with a live
     parent incidence is never released ("shared internal gates are released only when
     their last live incoming parent reference is retired") and that every retired
     incidence of a maintained gate is strictly dominated at all later times.

## Model

* Terminals are a type `Z` with an injective map `leaf : Z → ℕ` onto leaves of the circuit.
* An observation is a pair `(z, x)`.  The raw confidence interval of the terminal just
  sampled is an arbitrary function `ci` of the history (so Hoeffding, empirical-Bernstein
  and any other construction are covered).
* `boxStep` forms the running intersection `[max l a, min u b]`.  If the intersection is
  empty the box is left unchanged and a sticky `alarm` flag is raised (the manuscript's
  confidence alarm); the flag is part of every reply, so a controller may stop on it.
  Boxes are therefore nested and nonempty by construction.
* The controller model is `Representation.Controller`: the next terminal is any function
  of the history, the oracle reply and a controller tape.

The manuscript says "exact rollout trajectory coupling with unmonitored TA-UCT"; here this
is the statement that for every controller the run under the selective monitor equals the
run under the eager monitor (a controller that ignores the reply except for stopping is a
special case).
-/
import JointRootCert.RetireFinal

namespace JointRootCert
namespace LiteralK1

open Finset CostEngines DagRetire EngineFinal RetireFinal
open _root_.JointRootCert.Representation (Controller history replyAt stopTime OracleImpl exact_coupling)

/-! ## Congruence of circuit transformations at arbitrary gates -/

section Congruence

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma heapMax_eq_sup (cs : List ℕ) (v : ℕ → α) : heapMax cs v = cs.toFinset.sup v := by
  induction cs with
  | nil => simp [heapMax]
  | cons c cs ih => rw [heapMax_cons, ih, List.toFinset_cons, Finset.sup_insert]

lemma heapMax_map (cs : List ℕ) (f : ℕ → ℕ) (v : ℕ → α) :
    heapMax (cs.map f) v = heapMax cs (fun x => v (f x)) := by
  unfold heapMax
  rw [List.map_map]
  rfl

/-- Terminal support of a gate, with fuel. -/
def suppF (G : Dag) : ℕ → ℕ → Finset ℕ
  | 0, _ => ∅
  | n + 1, g =>
    if G.children g = [] then {g} else (G.children g).toFinset.biUnion (suppF G n)

/-- **Terminal support** of gate `g`: the leaves reachable from `g`. -/
def supp (G : Dag) (g : ℕ) : Finset ℕ := suppF G (G.level g + 1) g

lemma suppF_fuel {G : Dag} (hG : G.WF) : ∀ n m g, G.level g < n → G.level g < m →
    suppF G n g = suppF G m g := by
  intro n
  induction n with
  | zero => intro m g h; omega
  | succ n ih =>
    intro m g hn hm
    cases m with
    | zero => omega
    | succ m =>
      simp only [suppF]
      split_ifs with hc
      · rfl
      · apply Finset.biUnion_congr rfl
        intro c hcm
        have := hG.level_lt g c (List.mem_toFinset.1 hcm)
        exact ih m c (by omega) (by omega)

lemma supp_leaf {G : Dag} {g : ℕ} (h : G.children g = []) : supp G g = {g} := by
  simp [supp, suppF, h]

lemma supp_gate {G : Dag} (hG : G.WF) {g : ℕ} (h : G.children g ≠ []) :
    supp G g = (G.children g).toFinset.biUnion (supp G) := by
  unfold supp
  rw [suppF, ite_eq_right h]
  apply Finset.biUnion_congr rfl
  intro c hc
  have := hG.level_lt g c (List.mem_toFinset.1 hc)
  exact suppF_fuel hG _ _ c this (Nat.lt_succ_self _)

/-- **A gate of a max-circuit DAG computes the maximum over its terminal support**, for
every exact valuation. -/
theorem exact_eq_sup {G : Dag} (hG : G.WF) {v : ℕ → α} (hv : Exact G v) :
    ∀ g, v g = (supp G g).sup v := by
  have key : ∀ n g, G.level g < n → v g = (supp G g).sup v := by
    intro n
    induction n with
    | zero => intro g h; omega
    | succ n ih =>
      intro g hg
      by_cases hc : G.children g = []
      · rw [supp_leaf hc, Finset.sup_singleton]
      · rw [hv g hc, supp_gate hG hc, Finset.sup_biUnion, heapMax_eq_sup]
        apply Finset.sup_congr rfl
        intro c hcm
        exact ih c (by have := hG.level_lt g c (List.mem_toFinset.1 hcm); omega)
  exact fun g => key _ g (Nat.lt_succ_self _)

/-- Gates of two circuits with the same terminal support hold the same value whenever the
two exact valuations agree on that support. -/
theorem exact_eq_of_supp_eq {G G' : Dag} (hG : G.WF) (hG' : G'.WF) {v v' : ℕ → α}
    (hv : Exact G v) (hv' : Exact G' v') {g g' : ℕ} (hs : supp G' g' = supp G g)
    (hl : ∀ x ∈ supp G g, v' x = v x) : v' g' = v g := by
  rw [exact_eq_sup hG' hv' g', exact_eq_sup hG hv g, hs]
  exact Finset.sup_congr rfl hl

/-- `G'` computes the same function as `G`: every exact valuation of `G` is an exact
valuation of `G'`. -/
def Refines (α : Type*) [LinearOrder α] [OrderBot α] (G G' : Dag) : Prop :=
  ∀ v : ℕ → α, Exact G v → Exact G' v

theorem Refines.trans {G G' G'' : Dag} (h : Refines α G G') (h' : Refines α G' G'') :
    Refines α G G'' := fun v hv => h' v (h v hv)

/-- **Local rewrites give a refinement.**  If every internal gate of `G'` is an internal
gate of `G` whose child list was rewritten without changing its heap maximum on exact
valuations of `G` (the three moves below, at any gate, or no change), then `G'` computes
the same function as `G`. -/
theorem refines_of_local {G G' : Dag}
    (h : ∀ g, G'.children g ≠ [] → G.children g ≠ [] ∧
      ∀ v : ℕ → α, Exact G v → heapMax (G'.children g) v = heapMax (G.children g) v) :
    Refines α G G' :=
  fun v hv g hg => (hv g (h g hg).1).trans ((h g hg).2 v hv).symm

/-- Replace every occurrence of `c` in a child list by `d`. -/
def subst (c d : ℕ) (cs : List ℕ) : List ℕ := cs.map (fun x => if x = c then d else x)

lemma heapMax_subst {v : ℕ → α} {c d : ℕ} (h : v c = v d) (cs : List ℕ) :
    heapMax (subst c d cs) v = heapMax cs v := by
  unfold subst
  rw [heapMax_map]
  apply heapMax_congr
  intro x _
  show v (if x = c then d else x) = v x
  split_ifs with e
  · rw [e, h]
  · rfl

/-- **Unary bypass at any gate.**  If `c` is a unary gate with child `d`, replacing `c` by
`d` in the child list of any gate leaves that gate's maximum unchanged. -/
theorem bypass_move {G : Dag} {v : ℕ → α} (hv : Exact G v) {c d : ℕ}
    (hc : G.children c = [d]) (cs : List ℕ) : heapMax (subst c d cs) v = heapMax cs v := by
  apply heapMax_subst
  rw [hv c (by rw [hc]; simp), hc]
  simp [heapMax]

/-- **Interning at any gate.**  If `g₁` and `g₂` have the same child set, replacing `g₂`
by `g₁` in the child list of any gate leaves that gate's maximum unchanged. -/
theorem intern_move {G : Dag} {v : ℕ → α} (hv : Exact G v) {g1 g2 : ℕ}
    (hne : G.children g1 ≠ []) (hsame : ∀ c, c ∈ G.children g1 ↔ c ∈ G.children g2)
    (cs : List ℕ) : heapMax (subst g2 g1 cs) v = heapMax cs v := by
  apply heapMax_subst
  have hne2 : G.children g2 ≠ [] := by
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
    exact List.ne_nil_of_mem ((hsame c).1 hc)
  rw [hv g2 hne2, hv g1 hne]
  exact heapMax_eq_of_sub (fun c hc => (hsame c).1 hc) (fun c hc => Or.inl ((hsame c).2 hc))

/-- **Dyadic-block replacement at any gate.**  If the gates `bs` (for instance shared
dyadic-block gates) have terminal supports whose union is the terminal support of the
internal gate `p`, then `bs` may replace the child list of `p`. -/
theorem dyadic_move {G : Dag} (hG : G.WF) {v : ℕ → α} (hv : Exact G v) {p : ℕ}
    (hp : G.children p ≠ []) {bs : List ℕ}
    (hcover : bs.toFinset.biUnion (supp G) = supp G p) :
    heapMax bs v = heapMax (G.children p) v := by
  rw [← hv p hp, exact_eq_sup hG hv p, ← hcover, Finset.sup_biUnion, heapMax_eq_sup]
  exact Finset.sup_congr rfl (fun b _ => exact_eq_sup hG hv b)

/-- **Congruence for the eager engines.**  If `G'` computes the same function as `G`, has
the same leaves, and the two full-incidence engines start from states with the same leaf
values, then along any update sequence they store the same lower and upper value at every
gate at every time. -/
theorem eager_refines {G G' : Dag} (hG : G.WF) (hG' : G'.WF) (href : Refines α G G')
    (hleaves : ∀ g, G'.children g = [] ↔ G.children g = [])
    {s0 s0' : EState α × EState α}
    (i1 : Inv G s0.1) (i2 : Inv G s0.2) (i1' : Inv G' s0'.1) (i2' : Inv G' s0'.2)
    (hl0 : ∀ g, G.children g = [] → s0'.1.val g = s0.1.val g ∧ s0'.2.val g = s0.2.val g)
    (u : ℕ → ℕ × α × α) (hu : ∀ t, (u (t + 1)).1 < G.N ∧ (u (t + 1)).1 < G'.N) : ∀ t g,
    (runState G' u s0' t).1.val g = (runState G u s0 t).1.val g ∧
    (runState G' u s0' t).2.val g = (runState G u s0 t).2.val g := by
  have key : ∀ t, Inv G (runState G u s0 t).1 ∧ Inv G (runState G u s0 t).2 ∧
      Inv G' (runState G' u s0' t).1 ∧ Inv G' (runState G' u s0' t).2 ∧
      ∀ g, G.children g = [] →
        (runState G' u s0' t).1.val g = (runState G u s0 t).1.val g ∧
        (runState G' u s0' t).2.val g = (runState G u s0 t).2.val g := by
    intro t
    induction t with
    | zero => exact ⟨i1, i2, i1', i2', hl0⟩
    | succ t ih =>
      obtain ⟨a1, a2, a1', a2', al⟩ := ih
      obtain ⟨hx, hx'⟩ := hu t
      obtain ⟨l1, l2, l3, _⟩ := wave_spec hG (u (t + 1)).1 (u (t + 1)).2.1 _ hx a1
      obtain ⟨h1, h2, h3, _⟩ := wave_spec hG (u (t + 1)).1 (u (t + 1)).2.2 _ hx a2
      obtain ⟨l1', l2', l3', _⟩ := wave_spec hG' (u (t + 1)).1 (u (t + 1)).2.1 _ hx' a1'
      obtain ⟨h1', h2', h3', _⟩ := wave_spec hG' (u (t + 1)).1 (u (t + 1)).2.2 _ hx' a2'
      refine ⟨l1, h1, l1', h1', fun g hg => ?_⟩
      have hg' : G'.children g = [] := (hleaves g).2 hg
      by_cases e : g = (u (t + 1)).1
      · rw [e] at hg hg' ⊢
        exact ⟨(l2' hg').trans (l2 hg).symm, (h2' hg').trans (h2 hg).symm⟩
      · exact ⟨(l3' g hg' e).trans (((al g hg).1).trans (l3 g hg e).symm),
          (h3' g hg' e).trans (((al g hg).2).trans (h3 g hg e).symm)⟩
  intro t g
  obtain ⟨a1, a2, a1', a2', al⟩ := key t
  exact ⟨exact_unique hG' (inv_exact a1') (href _ (inv_exact a1))
      (fun g hg => (al g ((hleaves g).1 hg)).1) g,
    exact_unique hG' (inv_exact a2') (href _ (inv_exact a2))
      (fun g hg => (al g ((hleaves g).1 hg)).2) g⟩

end Congruence

/-! ## Running-intersection terminal boxes -/

section Box

variable {Z X α : Type*} [DecidableEq Z] [LinearOrder α]

/-- The terminal box: endpoints, the sticky confidence-alarm flag and the history. -/
structure BoxState (Z X α : Type*) where
  lo : Z → α
  hi : Z → α
  alarm : Bool
  hist : List (Z × X)

/-- The initial box `I₀`. -/
def box0 (I0 : Z → α × α) : BoxState Z X α := ⟨fun z => (I0 z).1, fun z => (I0 z).2, false, []⟩

/-- **Running intersection** (`eq:terminal-box`).  The raw interval `ci` of the terminal
just sampled is intersected with its current interval; an empty intersection leaves the
box unchanged and raises the alarm. -/
def boxStep (ci : List (Z × X) → α × α) (b : BoxState Z X α) (o : Z × X) : BoxState Z X α :=
  if max (b.lo o.1) (ci (b.hist ++ [o])).1 ≤ min (b.hi o.1) (ci (b.hist ++ [o])).2 then
    ⟨Function.update b.lo o.1 (max (b.lo o.1) (ci (b.hist ++ [o])).1),
     Function.update b.hi o.1 (min (b.hi o.1) (ci (b.hist ++ [o])).2), b.alarm, b.hist ++ [o]⟩
  else ⟨b.lo, b.hi, true, b.hist ++ [o]⟩

/-- The boxes are nested, change only at the sampled terminal, and stay nonempty. -/
lemma boxStep_facts (ci : List (Z × X) → α × α) (b : BoxState Z X α) (o : Z × X) :
    (∀ z, b.lo z ≤ (boxStep ci b o).lo z) ∧ (∀ z, (boxStep ci b o).hi z ≤ b.hi z) ∧
    (∀ z, z ≠ o.1 → (boxStep ci b o).lo z = b.lo z ∧ (boxStep ci b o).hi z = b.hi z) ∧
    ((∀ z, b.lo z ≤ b.hi z) → ∀ z, (boxStep ci b o).lo z ≤ (boxStep ci b o).hi z) ∧
    (boxStep ci b o).hist = b.hist ++ [o] := by
  unfold boxStep
  split_ifs with h
  · refine ⟨fun z => ?_, fun z => ?_, fun z hz => ?_, fun hb z => ?_, rfl⟩
    · show b.lo z ≤ Function.update b.lo o.1 _ z
      by_cases e : z = o.1
      · rw [e, Function.update_self]; exact le_max_left _ _
      · rw [Function.update_of_ne e]
    · show Function.update b.hi o.1 _ z ≤ b.hi z
      by_cases e : z = o.1
      · rw [e, Function.update_self]; exact min_le_left _ _
      · rw [Function.update_of_ne e]
    · exact ⟨Function.update_of_ne hz _ _, Function.update_of_ne hz _ _⟩
    · show Function.update b.lo o.1 _ z ≤ Function.update b.hi o.1 _ z
      by_cases e : z = o.1
      · rw [e, Function.update_self, Function.update_self]; exact h
      · rw [Function.update_of_ne e, Function.update_of_ne e]; exact hb z
  · exact ⟨fun _ => le_rfl, fun _ => le_rfl, fun _ _ => ⟨rfl, rfl⟩, fun hb => hb, rfl⟩

/-- The box after the first `t` observations of a stream. -/
def boxAt (ci : List (Z × X) → α × α) (b0 : BoxState Z X α) (obs : ℕ → Z × X) :
    ℕ → BoxState Z X α
  | 0 => b0
  | t + 1 => boxStep ci (boxAt ci b0 obs t) (obs t)

lemma boxAt_hist_length (ci : List (Z × X) → α × α) (b0 : BoxState Z X α) (hb : b0.hist = [])
    (obs : ℕ → Z × X) : ∀ t, (boxAt ci b0 obs t).hist.length = t := by
  intro t
  induction t with
  | zero => simp [boxAt, hb]
  | succ t ih =>
    show (boxStep ci (boxAt ci b0 obs t) (obs t)).hist.length = t + 1
    rw [(boxStep_facts ci _ _).2.2.2.2, List.length_append, ih]
    rfl

end Box

/-! ## The two engines as oracle implementations -/

section Engines

variable {Z X : Type*} [DecidableEq Z] {α : Type*} [LinearOrder α] [OrderBot α]

/-- Terminal updates fed to the engines along a stream of observations: rollout `t + 1`
writes the new box endpoints of the terminal it sampled. -/
def uS (leaf : Z → ℕ) (ci : List (Z × X) → α × α) (b0 : BoxState Z X α) (obs : ℕ → Z × X) :
    ℕ → ℕ × α × α
  | 0 => (0, ⊥, ⊥)
  | t + 1 => (leaf (obs t).1, (boxAt ci b0 obs (t + 1)).lo (obs t).1,
      (boxAt ci b0 obs (t + 1)).hi (obs t).1)

/-- One observation processed by the Graph-Selective engine: box update; root retirement
with release if a query is scheduled (`q`); waves on the live circuit; strict-dominance
retirement pass over the candidates of `cand`; release cascade. -/
def selStep (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ)) (q : ℕ → Bool)
    (leaf : Z → ℕ) (ci : List (Z × X) → α × α) (s : BoxState Z X α × QS α) (o : Z × X) :
    BoxState Z X α × QS α :=
  (boxStep ci s.1 o,
   (relStep K rt cand (leaf o.1, (boxStep ci s.1 o).lo o.1, (boxStep ci s.1 o).hi o.1)
      (if q s.1.hist.length = true then (qRetire K rt s.2).1 else s.2)).1)

/-- One observation processed by the Graph-Eager engine: box update and full-incidence
waves on the original circuit. -/
def eagStep (G0 : Dag) (leaf : Z → ℕ) (ci : List (Z × X) → α × α)
    (s : BoxState Z X α × (EState α × EState α)) (o : Z × X) :
    BoxState Z X α × (EState α × EState α) :=
  (boxStep ci s.1 o,
   (ivWave G0 (leaf o.1) ((boxStep ci s.1 o).lo o.1) ((boxStep ci s.1 o).hi o.1) s.2).1)

/-- **Graph-Selective as an oracle implementation.**  The reply is the alarm flag, the
lowest-index lower-bound leader among the active root actions and the marginal stopping
bit, read from the stored values of the active root gates only. -/
noncomputable def selImpl (G0 : Dag) (K : ℕ) (rt : ℕ → ℕ)
    (cand : RState α → RState α → List (ℕ × ℕ)) (q : ℕ → Bool) (leaf : Z → ℕ)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α) (lo0 hi0 : EState α) (φ : α → ℝ) (ε : ℝ) :
    OracleImpl (BoxState Z X α × QS α) (Z × X) (Bool × Option ℕ × Bool) where
  init := (box0 I0, ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩)
  step := selStep K rt cand q leaf ci
  reply := fun s => (s.1.alarm,
    qOut φ ε K (fun i => s.2.r.lo.val (rt i)) (fun i => s.2.r.hi.val (rt i)) s.2.act)

/-- **Graph-Eager as an oracle implementation**: same reply, read from the values of all
root gates of the full-incidence engine. -/
noncomputable def eagImpl (G0 : Dag) (K : ℕ) (rt : ℕ → ℕ) (leaf : Z → ℕ)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α) (lo0 hi0 : EState α) (φ : α → ℝ) (ε : ℝ) :
    OracleImpl (BoxState Z X α × (EState α × EState α)) (Z × X) (Bool × Option ℕ × Bool) where
  init := (box0 I0, (lo0, hi0))
  step := eagStep G0 leaf ci
  reply := fun s => (s.1.alarm,
    qOut φ ε K (fun i => s.2.1.val (rt i)) (fun i => s.2.2.val (rt i)) (fun _ => true))

/-- Numerical reply of the selective engine: alarm and the stored interval of every root
gate. -/
def selImplNum (G0 : Dag) (K : ℕ) (rt : ℕ → ℕ)
    (cand : RState α → RState α → List (ℕ × ℕ)) (leaf : Z → ℕ)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α) (lo0 hi0 : EState α) :
    OracleImpl (BoxState Z X α × QS α) (Z × X) (Bool × (Fin K → α × α)) where
  init := (box0 I0, ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩)
  step := selStep K rt cand (fun _ => false) leaf ci
  reply := fun s => (s.1.alarm, fun i => (s.2.r.lo.val (rt i), s.2.r.hi.val (rt i)))

/-- Numerical reply of the eager engine. -/
def eagImplNum (G0 : Dag) (K : ℕ) (rt : ℕ → ℕ) (leaf : Z → ℕ)
    (ci : List (Z × X) → α × α) (I0 : Z → α × α) (lo0 hi0 : EState α) :
    OracleImpl (BoxState Z X α × (EState α × EState α)) (Z × X) (Bool × (Fin K → α × α)) where
  init := (box0 I0, (lo0, hi0))
  step := eagStep G0 leaf ci
  reply := fun s => (s.1.alarm, fun i => (s.2.1.val (rt i), s.2.2.val (rt i)))

variable {G0 : Dag} {K : ℕ} {rt : ℕ → ℕ} {cand : RState α → RState α → List (ℕ × ℕ)}
  {q : ℕ → Bool} {leaf : Z → ℕ} {ci : List (Z × X) → α × α} {I0 : Z → α × α}
  {lo0 hi0 : EState α}

lemma sel_fold (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ)) (q : ℕ → Bool)
    (leaf : Z → ℕ) (ci : List (Z × X) → α × α) (b0 : BoxState Z X α) (hb : b0.hist = [])
    (s0 : QS α) (obs : ℕ → Z × X) : ∀ n,
    ((List.range n).map obs).foldl (selStep K rt cand q leaf ci) (b0, s0)
      = (boxAt ci b0 obs n, runF K rt cand (uS leaf ci b0 obs) q s0 n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, selStep]
    rw [boxAt_hist_length ci b0 hb obs n]
    rfl

lemma eag_fold (G0 : Dag) (leaf : Z → ℕ) (ci : List (Z × X) → α × α) (b0 : BoxState Z X α)
    (e0 : EState α × EState α) (obs : ℕ → Z × X) : ∀ n,
    ((List.range n).map obs).foldl (eagStep G0 leaf ci) (b0, e0)
      = (boxAt ci b0 obs n, runState G0 (uS leaf ci b0 obs) e0 n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, eagStep]
    rfl

lemma list_eq_map_range {β : Type*} (h : List β) (d : β) :
    (List.range h.length).map (fun t => h.getD t d) = h := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [List.getD_eq_getElem?_getD, h1]

/-- **Invariant of the reference run along a stream.**  The engine without retirement
keeps its invariant, its terminal gates store the running-intersection box, and the box is
nonempty.  Nothing is assumed about the stream. -/
theorem stream_inv (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (obs : ℕ → Z × X) : ∀ t,
    RInv G0 (rrun noCand (uS leaf ci (box0 I0) obs) ⟨G0, lo0, hi0⟩ t) ∧
    (∀ z, (rrun noCand (uS leaf ci (box0 I0) obs) ⟨G0, lo0, hi0⟩ t).lo.val (leaf z)
        = (boxAt ci (box0 I0) obs t).lo z ∧
      (rrun noCand (uS leaf ci (box0 I0) obs) ⟨G0, lo0, hi0⟩ t).hi.val (leaf z)
        = (boxAt ci (box0 I0) obs t).hi z) ∧
    (∀ z, (boxAt ci (box0 I0) obs t).lo z ≤ (boxAt ci (box0 I0) obs t).hi z) := by
  intro t
  induction t with
  | zero =>
    refine ⟨h0, hI0, fun z => ?_⟩
    show (I0 z).1 ≤ (I0 z).2
    rw [← (hI0 z).1, ← (hI0 z).2]
    exact h0.cons (leaf z)
  | succ t ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    obtain ⟨f1, f2, f3, f4, _⟩ := boxStep_facts ci (boxAt ci (box0 I0) obs t) (obs t)
    have hx := (hleaf (obs t).1).1
    have hw := waveStep_inv ih1 (uS leaf ci (box0 I0) obs (t + 1)) hx
      (((ih2 (obs t).1).1).le.trans (f1 _)) (f4 ih3 _)
      ((f2 _).trans ((ih2 (obs t).1).2).ge)
    have e : rrun noCand (uS leaf ci (box0 I0) obs) ⟨G0, lo0, hi0⟩ (t + 1)
        = (waveStep (uS leaf ci (box0 I0) obs (t + 1))
            (rrun noCand (uS leaf ci (box0 I0) obs) ⟨G0, lo0, hi0⟩ t)).1 := rfl
    obtain ⟨_, l2, l3, _⟩ := wave_spec ih1.wf (leaf (obs t).1)
      ((boxAt ci (box0 I0) obs (t + 1)).lo (obs t).1) _ (ih1.nEq ▸ hx) ih1.invLo
    obtain ⟨_, u2, u3, _⟩ := wave_spec ih1.wf (leaf (obs t).1)
      ((boxAt ci (box0 I0) obs (t + 1)).hi (obs t).1) _ (ih1.nEq ▸ hx) ih1.invHi
    refine ⟨e ▸ hw, fun z => ?_, f4 ih3⟩
    have hls : (rrun noCand (uS leaf ci (box0 I0) obs) ⟨G0, lo0, hi0⟩ t).G.children (leaf z)
        = [] := (ih1.leaf_iff _).2 (hleaf z).2
    rw [e]
    by_cases hz : z = (obs t).1
    · rw [hz] at hls ⊢
      exact ⟨l2 hls, u2 hls⟩
    · have hne : leaf z ≠ leaf (obs t).1 := fun h => hz (hinj h)
      exact ⟨(l3 _ hls hne).trans (((ih2 z).1).trans (f3 z hz).1.symm),
        (u3 _ hls hne).trans (((ih2 z).2).trans (f3 z hz).2.symm)⟩

/-- **Nestedness is derived, not assumed.**  The updates produced by the
running-intersection box along any stream of observations form a `NestedRun`. -/
theorem stream_nested (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (obs : ℕ → Z × X) :
    NestedRun G0 noCand (uS leaf ci (box0 I0) obs) ⟨G0, lo0, hi0⟩ := by
  intro t
  obtain ⟨_, ih2, ih3⟩ := stream_inv (ci := ci) h0 hleaf hinj hI0 obs t
  obtain ⟨f1, f2, _, f4, _⟩ := boxStep_facts ci (boxAt ci (box0 I0) obs t) (obs t)
  exact ⟨(hleaf (obs t).1).1, ((ih2 (obs t).1).1).le.trans (f1 _), f4 ih3 _,
    (f2 _).trans ((ih2 (obs t).1).2).ge⟩

/-- **Facts about the Graph-Selective run** (any candidate policy, any query schedule, any
stream of observations).  At every time:

* the gate of every active root action stores the interval of the eager engine;
* every gate with a live parent incidence is not released and stores the interval of the
  eager engine: a shared gate is released only after its last live parent reference is
  gone;
* every incidence `(p, c)` that has been unlinked from a gate `p` that is still maintained
  is strictly dominated in the current exact valuation, `u(c) < l(p)`. -/
theorem selective_run_facts (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (obs : ℕ → Z × X) (t : ℕ) :
    let u := uS leaf ci (box0 I0) obs
    let S := runF K rt cand u q ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ t
    let E := runState G0 u (lo0, hi0) t
    (∀ i, i < K → S.act i = true →
      S.r.lo.val (rt i) = E.1.val (rt i) ∧ S.r.hi.val (rt i) = E.2.val (rt i)) ∧
    (∀ p c, c ∈ S.r.G.children p → ¬ Dead G0 S.r.G c ∧
      S.r.lo.val c = E.1.val c ∧ S.r.hi.val c = E.2.val c) ∧
    (∀ p c, c ∈ G0.children p → c ∉ S.r.G.children p → ¬ Dead G0 S.r.G p →
      E.2.val c < E.1.val p) := by
  intro u S E
  have hn := stream_nested (ci := ci) h0 hleaf hinj hI0 obs
  have hinv := runF_inv (K := K) (rt := rt) (cand := cand) (q := q)
    (act0 := fun _ => true) hG h0 hn t
  obtain ⟨_, _, e3, e4⟩ := live_eq_eager hG h0 hn t
  refine ⟨fun i hi ha => ?_, fun p c hc => ?_, fun p c hc hnc hd => ?_⟩
  · obtain ⟨a, b⟩ := hinv.agree (rt i) (hinv.prot i hi ha)
    exact ⟨a.trans (e3 _), b.trans (e4 _)⟩
  · have hd := hinv.live_child p c hc
    obtain ⟨a, b⟩ := hinv.agree c hd
    exact ⟨hd, a.trans (e3 _), b.trans (e4 _)⟩
  · have := hinv.dom p c hc hnc hd
    rw [e3, e4] at this
    exact this

/-- **Graph-Selective and Graph-Eager expose the same leader-and-stop oracle on every
history.** -/
theorem sel_answer_eq (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε) (h : List (Z × X)) :
    (selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer h
      = (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer h := by
  have stream : ∀ (obs : ℕ → Z × X) (n : ℕ),
      (selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer ((List.range n).map obs)
        = (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ((List.range n).map obs) := by
    intro obs n
    have hn := stream_nested (ci := ci) h0 hleaf hinj hI0 obs
    simp only [OracleImpl.answer, selImpl, eagImpl]
    rw [sel_fold K rt cand q leaf ci (box0 I0) rfl _ obs n,
      eag_fold G0 leaf ci (box0 I0) _ obs n]
    show (_, qOut φ ε K _ _ _) = (_, qOut φ ε K _ _ _)
    rw [query_coupling hG h0 hn hK φ hφ ε hε n]
    obtain ⟨_, _, e3, e4⟩ := live_eq_eager hG h0 hn n
    have f1 := funext e3
    have f2 := funext e4
    rw [f1, f2]
  rcases h with _ | ⟨d, h'⟩
  · rfl
  · have := stream (fun t => (d :: h').getD t d) (d :: h').length
    rwa [list_eq_map_range] at this

/-- **`prop:representation-coupling`, retirement clause.**  Let `G0` be a well-formed
max-circuit DAG (gates may be shared) whose terminals `leaf z` are leaves, and let the
engine start from an initialised state (`RInv`, as produced by `DagRetire.init_engine`)
whose terminal gates hold the initial box `I₀`.  Then for every candidate policy `cand` of
the strict-dominance rule `u(c) < l(v)`, every query schedule `q`, every raw
confidence-interval construction `ci`, every controller, reward tape and controller tape,
the run monitored by the Graph-Selective engine (retirement, release of orphaned gates,
root-action retirement) and the run monitored by the Graph-Eager engine have identical
histories (rollout trajectories and terminal rewards), identical replies (alarm, leader,
stopping bit) and identical stopping times.  Needs `ε ≥ 0` and at least one root action. -/
theorem retirement_coupling_literal {Ω : Type*} (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (ctrl : Controller Z X (Bool × Option ℕ × Bool) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n
        = history (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    (∀ n, replyAt (selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n
        = replyAt (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    stopTime (selImpl G0 K rt cand q leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω
      = stopTime (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω :=
  exact_coupling _ _ (sel_answer_eq hG h0 hleaf hinj hI0 hK φ hφ ε hε) ctrl rew ω

lemma runF_act_noquery (K : ℕ) (rt : ℕ → ℕ) (cand : RState α → RState α → List (ℕ × ℕ))
    (u : ℕ → ℕ × α × α) (s0 : QS α) : ∀ t,
    (runF K rt cand u (fun _ => false) s0 t).act = s0.act := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => exact ih

/-- **Numerical coupling with protected roots**: with internal retirement and release but
no root retirement, the selective engine exposes the same interval for every root action
as the eager engine, on every history. -/
theorem sel_answer_num_eq (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (h : List (Z × X)) :
    (selImplNum G0 K rt cand leaf ci I0 lo0 hi0).answer h
      = (eagImplNum G0 K rt leaf ci I0 lo0 hi0).answer h := by
  have stream : ∀ (obs : ℕ → Z × X) (n : ℕ),
      (selImplNum G0 K rt cand leaf ci I0 lo0 hi0).answer ((List.range n).map obs)
        = (eagImplNum G0 K rt leaf ci I0 lo0 hi0).answer ((List.range n).map obs) := by
    intro obs n
    obtain ⟨hr, _, _⟩ := selective_run_facts (K := K) (rt := rt) (cand := cand)
      (q := fun _ => false) (ci := ci) hG h0 hleaf hinj hI0 obs n
    have hact := runF_act_noquery K rt cand (uS leaf ci (box0 I0) obs)
      ⟨⟨G0, lo0, hi0⟩, fun _ => true⟩ n
    simp only [OracleImpl.answer, selImplNum, eagImplNum]
    rw [sel_fold K rt cand (fun _ => false) leaf ci (box0 I0) rfl _ obs n,
      eag_fold G0 leaf ci (box0 I0) _ obs n]
    refine Prod.ext rfl (funext fun i => ?_)
    obtain ⟨a, b⟩ := hr i i.isLt (by rw [hact])
    exact Prod.ext a b
  rcases h with _ | ⟨d, h'⟩
  · rfl
  · have := stream (fun t => (d :: h').getD t d) (d :: h').length
    rwa [list_eq_map_range] at this

/-- **`prop:representation-coupling`, numerical form**: the selective engine with protected
root actions preserves all root confidence intervals, hence the run of any controller that
reads them. -/
theorem interval_coupling_literal {Ω : Type*} (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hleaf : ∀ z, leaf z < G0.N ∧ G0.children (leaf z) = []) (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (ctrl : Controller Z X (Bool × (Fin K → α × α)) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (selImplNum G0 K rt cand leaf ci I0 lo0 hi0).answer ctrl rew ω n
        = history (eagImplNum G0 K rt leaf ci I0 lo0 hi0).answer ctrl rew ω n) ∧
    (∀ n, replyAt (selImplNum G0 K rt cand leaf ci I0 lo0 hi0).answer ctrl rew ω n
        = replyAt (eagImplNum G0 K rt leaf ci I0 lo0 hi0).answer ctrl rew ω n) ∧
    stopTime (selImplNum G0 K rt cand leaf ci I0 lo0 hi0).answer ctrl rew ω
      = stopTime (eagImplNum G0 K rt leaf ci I0 lo0 hi0).answer ctrl rew ω :=
  exact_coupling _ _ (sel_answer_num_eq hG h0 hleaf hinj hI0) ctrl rew ω

/-- The eager engines on two circuits computing the same function expose the same oracle
on every history. -/
theorem eag_answer_refines {G1 : Dag} (hG : G0.WF) (hG1 : G1.WF) (href : Refines α G0 G1)
    (hleaves : ∀ g, G1.children g = [] ↔ G0.children g = [])
    {lo1 hi1 : EState α} (i1 : Inv G0 lo0) (i2 : Inv G0 hi0) (i1' : Inv G1 lo1)
    (i2' : Inv G1 hi1)
    (hl0 : ∀ g, G0.children g = [] → lo1.val g = lo0.val g ∧ hi1.val g = hi0.val g)
    (hleaf : ∀ z, leaf z < G0.N ∧ leaf z < G1.N) (φ : α → ℝ) (ε : ℝ) (h : List (Z × X)) :
    (eagImpl G1 K rt leaf ci I0 lo1 hi1 φ ε).answer h
      = (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer h := by
  have stream : ∀ (obs : ℕ → Z × X) (n : ℕ),
      (eagImpl G1 K rt leaf ci I0 lo1 hi1 φ ε).answer ((List.range n).map obs)
        = (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ((List.range n).map obs) := by
    intro obs n
    have hr := eager_refines (s0 := (lo0, hi0)) (s0' := (lo1, hi1)) hG hG1 href hleaves
      i1 i2 i1' i2' hl0 (uS leaf ci (box0 I0) obs) (fun t => hleaf (obs t).1) n
    simp only [OracleImpl.answer, eagImpl]
    rw [eag_fold G1 leaf ci (box0 I0) _ obs n, eag_fold G0 leaf ci (box0 I0) _ obs n]
    have f1 := funext (fun g => (hr g).1)
    have f2 := funext (fun g => (hr g).2)
    rw [f1, f2]
  rcases h with _ | ⟨d, h'⟩
  · have f1 : lo1.val = lo0.val := funext (exact_unique hG1 (inv_exact i1')
      (href _ (inv_exact i1)) (fun g hg => (hl0 g ((hleaves g).1 hg)).1))
    have f2 : hi1.val = hi0.val := funext (exact_unique hG1 (inv_exact i2')
      (href _ (inv_exact i2)) (fun g hg => (hl0 g ((hleaves g).1 hg)).2))
    show (false, qOut φ ε K (fun i => lo1.val (rt i)) (fun i => hi1.val (rt i)) (fun _ => true))
      = (false, qOut φ ε K (fun i => lo0.val (rt i)) (fun i => hi0.val (rt i)) (fun _ => true))
    rw [f1, f2]
  · have := stream (fun t => (d :: h').getD t d) (d :: h').length
    rwa [list_eq_map_range] at this

/-- **`prop:representation-coupling`, both sentences composed.**  Let `G1` be obtained
from the monitor circuit `G0` by unary bypass, interning and dyadic-block replacement at
any gates (so that `Refines α G0 G1`; see `refines_of_local`, `bypass_move`, `intern_move`,
`dyadic_move`), with the same leaves and root gates, and let both engines be initialised on
the same terminal intervals.  Then the Graph-Selective engine with strict-dominance
retirement INSIDE the transformed circuit `G1` and the Graph-Eager engine on the original
circuit `G0` induce identical histories, replies (alarm, leader, stopping bit) and
stopping times for every controller, reward tape and controller tape. -/
theorem representation_coupling_literal {Ω : Type*} {G1 : Dag} (hG : G0.WF) (hG1 : G1.WF)
    (href : Refines α G0 G1) (hleaves : ∀ g, G1.children g = [] ↔ G0.children g = [])
    {lo1 hi1 : EState α} (i1 : Inv G0 lo0) (i2 : Inv G0 hi0)
    (h1 : RInv G1 ⟨G1, lo1, hi1⟩)
    (hl0 : ∀ g, G0.children g = [] → lo1.val g = lo0.val g ∧ hi1.val g = hi0.val g)
    (hleaf : ∀ z, leaf z < G0.N ∧ leaf z < G1.N ∧ G0.children (leaf z) = [])
    (hinj : Function.Injective leaf)
    (hI0 : ∀ z, lo0.val (leaf z) = (I0 z).1 ∧ hi0.val (leaf z) = (I0 z).2)
    (hK : 0 < K) (φ : α → ℝ) (hφ : StrictMono φ) (ε : ℝ) (hε : 0 ≤ ε)
    (ctrl : Controller Z X (Bool × Option ℕ × Bool) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (selImpl G1 K rt cand q leaf ci I0 lo1 hi1 φ ε).answer ctrl rew ω n
        = history (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    (∀ n, replyAt (selImpl G1 K rt cand q leaf ci I0 lo1 hi1 φ ε).answer ctrl rew ω n
        = replyAt (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω n) ∧
    stopTime (selImpl G1 K rt cand q leaf ci I0 lo1 hi1 φ ε).answer ctrl rew ω
      = stopTime (eagImpl G0 K rt leaf ci I0 lo0 hi0 φ ε).answer ctrl rew ω := by
  apply exact_coupling
  intro h
  have hleaf1 : ∀ z, leaf z < G1.N ∧ G1.children (leaf z) = [] :=
    fun z => ⟨(hleaf z).2.1, (hleaves _).2 (hleaf z).2.2⟩
  have hI1 : ∀ z, lo1.val (leaf z) = (I0 z).1 ∧ hi1.val (leaf z) = (I0 z).2 := fun z =>
    ⟨((hl0 _ (hleaf z).2.2).1).trans (hI0 z).1, ((hl0 _ (hleaf z).2.2).2).trans (hI0 z).2⟩
  rw [sel_answer_eq hG1 h1 hleaf1 hinj hI1 hK φ hφ ε hε h]
  exact eag_answer_refines hG hG1 href hleaves i1 i2 h1.invLo h1.invHi hl0
    (fun z => ⟨(hleaf z).1, (hleaf z).2.1⟩) φ ε h

end Engines

end LiteralK1
end JointRootCert
