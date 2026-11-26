/-
Joint Root Certification: the work display `eq:ram-work-bounds`, with costed
initialisation, the sampler term, both engines on implemented heaps, and a wave scheduler
without level scans.

Manuscript result covered:

* `prop:uct-coupling` (Safe permanent retirement; also labelled `prop:ta-coupled`,
  `thm:protected-pruning`, `thm:decision-retirement`), the work-accounting paragraph of its
  proof and the display `eq:ram-work-bounds`.

IMPORTS `JointRootCert.LiteralE4a` (a new file; build it first).

## What is assembled (`ram_work_bounds_literal`)

For a trajectory `R : Traj α` (a well-formed DAG `G0` with duplicate-free child lists of
length at most `D`, its internal gates listed by nondecreasing level, initial terminal
intervals, `T` nested terminal updates, root queries at the times `t < T` with `q t`, `K ≥ 1`
root actions, a passive traversal policy `pick`):

* **Initialisation** is the costed program `EngineFinal.initPassH` (both endpoints; every
  heap built by `HeapImpl.insertAll`).  Its computed cost `R.initW` satisfies
  `initW ≤ 4 (|V| + (⌈log₂ D⌉ + 1) |E|)`.  This is `O(|V| + |E| log(2 + D))`, not
  `O(|V| + |E|)`: the heaps are built by insertion (a linear-time heap construction is not
  formalised).
* **Sampler**: rollout `t` walks the ORIGINAL circuit from `R.start t` to a terminal,
  evaluating one index per outgoing edge of each visited gate (`walk`).  Its cost
  `R.samp` satisfies `T ≤ samp ≤ T (L + 1)(D + 1)` and is the same number for both engines.
  It is `O(T)` only when depth times degree is bounded; the manuscript's term `T` has to be
  read as this traversal work.
* **Graph-Eager** is `runE`: full-incidence waves on implemented heaps with the sparse
  scheduler `waveS`, and a query that scans all `K` actions (`2K` units, by definition).
* **Graph-Selective** is `runS`: `waveS` waves on the live circuit, retirement tests and
  heap deletions (`EngineFinal.retireListH`), the release cascade
  (`RetireFinal.releaseLoopH`) and root retirement at queries (`RetireFinal.qRetireH`).
* Both return the same leader and the same stopping bit at every time.
* `T + S₀ ≤ W_eager ≤ initW + samp + 8T + 2QK + 2(⌈log₂ D⌉ + 3 + κ) S₀`,
  `T + S ≤ W_live ≤ initW + samp + 8T + 8QK + 2(⌈log₂ D⌉ + 5 + κ) S
      + 2(2⌈log₂ D⌉ + 4) R + 4(|V| + |E|)`, `S ≤ S₀`, `R ≤ |E|`,
  with `κ = ⌈log₂ (L + 1)⌉ + 3` the worklist charge per delivery of `waveS`.

There is no term `T · L`.  The differences from the manuscript's display are: `|E| log D`
in the initialisation, `samp` in place of `T`, and the factor `log(2 + D) + log(2 + L)` on
the deliveries in place of `log(2 + D)` (the worklist that orders the changed gates
topologically).  `bucket_engine_lower` shows that the level-bucket scheduler of
`CostEngines.wave` cannot meet the display.

Unit charges (by definition): one unit per index evaluation and per traversed edge of the
sampler; `2K` per eager query; the charges listed in `RetireFinal.lean`, `DagRetire.lean`
and `LiteralE4a.lean`.  Computed: all heap operations (gate heaps and level queue).
-/
import JointRootCert.LiteralE4a

namespace JointRootCert
namespace LiteralE4

open Finset CostEngines DagRetire EngineFinal RetireFinal
open HeapImpl (Heap HEState SimE Rep waveH findMax)

/-! ## The sampler: a passive traversal of the original circuit -/

section Sampler

/-- **One rollout of the passive traversal policy** on the circuit `G`, from gate `v`: at
an internal gate evaluate one index per outgoing edge (1 unit each) and follow the edge to
`pick v` (1 unit); stop at a terminal (1 unit).  Returns the terminal reached and the
cost.  The first argument is recursion fuel (`L + 1` suffices). -/
def walk (G : Dag) (pick : ℕ → ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, v => (v, 0)
  | f + 1, v =>
    if G.children v = [] then (v, 1)
    else ((walk G pick f (pick v)).1,
      (walk G pick f (pick v)).2 + (G.children v).length + 1)

/-- The traversal ends at a terminal; its cost is at least one unit and at most
`(level v + 1)(D + 1)`. -/
theorem walk_spec {G : Dag} (hG : G.WF) (D : ℕ) (hD : ∀ p, (G.children p).length ≤ D)
    (pick : ℕ → ℕ) (hpick : ∀ v, G.children v ≠ [] → pick v ∈ G.children v) :
    ∀ f v, G.level v < f → G.children (walk G pick f v).1 = [] ∧
      1 ≤ (walk G pick f v).2 ∧ (walk G pick f v).2 ≤ (G.level v + 1) * (D + 1) := by
  intro f
  induction f with
  | zero => intro v hv; omega
  | succ f ih =>
    intro v hv
    rw [walk]
    by_cases hc : G.children v = []
    · rw [ite_eq_left hc]
      exact ⟨hc, le_rfl, Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)⟩
    · rw [ite_eq_right hc]
      have hlt := hG.level_lt v (pick v) (hpick v hc)
      obtain ⟨i1, i2, i3⟩ := ih (pick v) (by omega)
      have h1 : (G.level (pick v) + 1) * (D + 1) ≤ G.level v * (D + 1) :=
        Nat.mul_le_mul_right _ hlt
      have h2 : (G.level v + 1) * (D + 1) = G.level v * (D + 1) + (D + 1) := Nat.succ_mul _ _
      have h3 := hD v
      refine ⟨i1, ?_, ?_⟩
      · show 1 ≤ (walk G pick f (pick v)).2 + (G.children v).length + 1
        omega
      · show (walk G pick f (pick v)).2 + (G.children v).length + 1 ≤ _
        omega

/-- A traversal that starts at an internal gate of degree `d` costs more than `d`: the
index of every outgoing edge is evaluated. -/
theorem walk_ge_deg (G : Dag) (pick : ℕ → ℕ) (f v : ℕ) (hc : G.children v ≠ []) :
    (G.children v).length + 1 ≤ (walk G pick (f + 1) v).2 := by
  rw [walk, ite_eq_right hc]
  show (G.children v).length + 1 ≤ (walk G pick f (pick v)).2 + (G.children v).length + 1
  omega

end Sampler

/-! ## The Graph-Selective engine with the sparse scheduler -/

section EngineS

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The backup waves of one terminal update, with the sparse scheduler `waveS`. -/
def waveStepS (u : ℕ × α × α) (s : HRState α) : HRState α × ℕ :=
  (⟨s.G, (waveS s.G u.1 u.2.1 s.lo).1, (waveS s.G u.1 u.2.2 s.hi).1⟩,
   (waveS s.G u.1 u.2.1 s.lo).2 + (waveS s.G u.1 u.2.2 s.hi).2)

/-- The part of a rollout after the waves (as in `RetireFinal.relStepH`): the retirement
pass over the candidates of the policy on the post-wave state `w`, then the release
cascade from the children of the tested incidences. -/
def tailStep (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (s : HQS α) (w : HRState α) :
    HQS α × ℕ :=
  (⟨(releaseLoopH (protOf K rt s.act)
        (relFuel (retireListH (candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val) w).1.G
          ((candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val).map Prod.snd))
        ((candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val).map Prod.snd)
        (retireListH (candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val) w).1).1, s.act⟩,
   (retireListH (candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val) w).2
    + (releaseLoopH (protOf K rt s.act)
        (relFuel (retireListH (candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val) w).1.G
          ((candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val).map Prod.snd))
        ((candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val).map Prod.snd)
        (retireListH (candV s.r.G s.r.lo.val s.r.hi.val w.lo.val w.hi.val) w).1).2)

/-- **One rollout of the Graph-Selective engine with the sparse scheduler**: `waveS` waves,
then retirement pass and release cascade, all on implemented heaps. -/
def relStepS (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ × α × α) (s : HQS α) :
    HQS α × ℕ :=
  ((tailStep K rt candV s (waveStepS u s.r).1).1,
   (waveStepS u s.r).2 + (tailStep K rt candV s (waveStepS u s.r).1).2)

lemma relStepH_tail (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ × α × α) (s : HQS α) :
    (relStepH K rt candV u s).1 = (tailStep K rt candV s (waveStepH u s.r).1).1 := rfl

variable {K : ℕ} {rt : ℕ → ℕ}

/-- Cost of the part after the waves, against the charged costs of `RetireFinal`. -/
lemma tailStep_cost (candV : Policy α) {hs : HQS α} {s : QS α} (h : SimQ hs s)
    (u : ℕ × α × α) :
    (tailStep K rt candV hs (waveStepH u hs.r).1).2
      ≤ 2 * ((retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).2
        + (releaseLoop (protOf K rt s.act)
            (relFuel (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G
              ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd))
            ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd)
            (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G).2) := by
  obtain ⟨hr, hact⟩ := h
  obtain ⟨w1, _⟩ := waveStepH_sim hr u
  have hc : candV hs.r.G hs.r.lo.val hs.r.hi.val (waveStepH u hs.r).1.lo.val
      (waveStepH u hs.r).1.hi.val = liftCand candV s.r (waveStep u s.r).1 := by
    unfold liftCand
    rw [hr.G, hr.lo.val, hr.hi.val, w1.lo.val, w1.hi.val]
  obtain ⟨r1, r2⟩ := retireListH_sim (liftCand candV s.r (waveStep u s.r).1) w1
  have hG1 : (retireListH (liftCand candV s.r (waveStep u s.r).1) (waveStepH u hs.r).1).1.G
      = (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G := r1.G
  obtain ⟨_, l2⟩ := releaseLoopH_sim (protOf K rt s.act)
    (relFuel (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G
      ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd))
    ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd) _ _ r1
  unfold tailStep
  rw [hc, hG1, hact]
  show (retireListH _ (waveStepH u hs.r).1).2 + (releaseLoopH _ _ _ _).2 ≤ _
  rw [l2]
  omega

/-- **One rollout with the sparse scheduler.**  From an implemented state representing a
state that satisfies the coupled invariant: the rollout ends in exactly the state of
`RetireFinal.relStepH`; its computed cost exceeds twice the charged cost of
`RetireFinal.relStep` by at most `8 + 2κ · (live deliveries)`, AFTER the four level scans
`4 (L + 3)` of the two waves are removed; and it is at least the number of live
deliveries. -/
theorem relStepS_spec (candV : Policy α) {hs : HQS α} {s : QS α} (h : SimQ hs s) {G0 : Dag}
    {elo ehi : ℕ → α} (hinv : CInv G0 K rt s.r s.act elo ehi) (u : ℕ × α × α)
    (hx : u.1 < G0.N) :
    (relStepS K rt candV u hs).1 = (relStepH K rt candV u hs).1 ∧
    (relStepS K rt candV u hs).2 + 4 * (G0.L + 3)
      ≤ 8 + 2 * (kap G0 * (vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1
            + vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1))
        + 2 * (relStep K rt (liftCand candV) u s).2 ∧
    vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1
        + vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1
      ≤ (relStepS K rt candV u hs).2 := by
  have hGeq : hs.r.G = s.r.G := h.r.G
  have hxs : u.1 < s.r.G.N := by rw [hinv.nEq]; exact hx
  obtain ⟨l1, l2, l3⟩ := waveS_spec hinv.wf u.1 u.2.1 hs.r.lo s.r.lo hxs h.r.lo hinv.invLo
  obtain ⟨u1, u2, u3⟩ := waveS_spec hinv.wf u.1 u.2.2 hs.r.hi s.r.hi hxs h.r.hi hinv.invHi
  obtain ⟨_, _, _, lw⟩ := wave_spec hinv.wf u.1 u.2.1 s.r.lo hxs hinv.invLo
  obtain ⟨_, _, _, uw⟩ := wave_spec hinv.wf u.1 u.2.2 s.r.hi hxs hinv.invHi
  have hk : kap s.r.G = kap G0 := by unfold kap; rw [hinv.lEq]
  rw [hk] at l2 u2
  rw [hinv.lEq] at lw uw
  have hw : (waveStepS u hs.r).1 = (waveStepH u hs.r).1 := by
    unfold waveStepS waveStepH
    rw [hGeq, l1, u1]
  have tc := tailStep_cost (K := K) (rt := rt) candV h u
  rw [← hw] at tc
  have eS : (relStepS K rt candV u hs).2
      = (waveS s.r.G u.1 u.2.1 hs.r.lo).2 + (waveS s.r.G u.1 u.2.2 hs.r.hi).2
        + (tailStep K rt candV hs (waveStepS u hs.r).1).2 := by
    show (waveS hs.r.G u.1 u.2.1 hs.r.lo).2 + (waveS hs.r.G u.1 u.2.2 hs.r.hi).2
        + (tailStep K rt candV hs (waveStepS u hs.r).1).2 = _
    rw [hGeq]
  have eA : (relStep K rt (liftCand candV) u s).2
      = (wave s.r.G u.1 u.2.1 s.r.lo).2 + (wave s.r.G u.1 u.2.2 s.r.hi).2
        + (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).2
        + (releaseLoop (protOf K rt s.act)
            (relFuel (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G
              ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd))
            ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd)
            (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G).2 :=
    rfl
  have hexp := Nat.mul_add (kap G0) (vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1)
    (vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1)
  refine ⟨?_, ?_, ?_⟩
  · show (tailStep K rt candV hs (waveStepS u hs.r).1).1 = (relStepH K rt candV u hs).1
    rw [hw]
    rfl
  · have key : ∀ (S cl cu tl chl chu kvl kvu kv rl rel A wl wu L : ℕ), S = cl + cu + tl →
        cl ≤ 4 + 2 * chl + 2 * kvl → cu ≤ 4 + 2 * chu + 2 * kvu → tl ≤ 2 * (rl + rel) →
        A = wl + wu + rl + rel → wl = L + 3 + chl → wu = L + 3 + chu → kv = kvl + kvu →
        S + 4 * (L + 3) ≤ 8 + 2 * kv + 2 * A := by
      intros
      omega
    exact key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ eS l2 u2 tc eA lw uw hexp
  · omega

/-- State of the Graph-Selective engine with the sparse scheduler after `t` rollouts
(queries with root retirement as in `RetireFinal.runH`). -/
def runS (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : HQS α) : ℕ → HQS α
  | 0 => s0
  | t + 1 => (relStepS K rt candV (u (t + 1))
      (if q t = true then (qRetireH K rt (runS K rt candV u q s0 t)).1
        else runS K rt candV u q s0 t)).1

/-- Computed cost of the query of time `t` (if any: stop scan `K`, leader scan `K`,
retirement scan `K`, release cascade) and of rollout `t + 1`. -/
def costS (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : HQS α) (t : ℕ) : ℕ :=
  (if q t = true then K + (qRetireH K rt (runS K rt candV u q s0 t)).2 else 0)
    + (relStepS K rt candV (u (t + 1))
        (if q t = true then (qRetireH K rt (runS K rt candV u q s0 t)).1
          else runS K rt candV u q s0 t)).2

variable {G0 : Dag} {u : ℕ → ℕ × α × α} {lo0 hi0 : EState α}

/-- **The run with the sparse scheduler.**  At every time the engine is in exactly the
state of `RetireFinal.runH`; the cost of step `t` is at most
`8 + 2κ · volF t + 2 · costF t - 4 (L + 3)` and at least the live deliveries `volF t`. -/
theorem runS_spec (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (q : ℕ → Bool) (hr0 : HRState α)
    (hsim : SimR hr0 ⟨G0, lo0, hi0⟩) (act0 : ℕ → Bool) (t : ℕ) :
    runS K rt delivV u q ⟨hr0, act0⟩ t = runH K rt delivV u q ⟨hr0, act0⟩ t ∧
    costS K rt delivV u q ⟨hr0, act0⟩ t + 4 * (G0.L + 3)
      ≤ 8 + 2 * (kap G0 * volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)
        + 2 * costF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t ∧
    volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t ≤ costS K rt delivV u q ⟨hr0, act0⟩ t := by
  have hS := runH_sim (K := K) (rt := rt) delivV u q
    (hs0 := ⟨hr0, act0⟩) (s0 := ⟨⟨G0, lo0, hi0⟩, act0⟩) ⟨hsim, rfl⟩
  have hpre : ∀ t, SimQ
      (if q t = true then (qRetireH K rt (runH K rt delivV u q ⟨hr0, act0⟩ t)).1
        else runH K rt delivV u q ⟨hr0, act0⟩ t)
      (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t) := by
    intro t
    unfold preF
    by_cases hq : q t = true
    · rw [ite_eq_left hq, ite_eq_left hq]
      exact (qRetireH_sim K rt (hS t).1).1
    · rw [ite_eq_right hq, ite_eq_right hq]
      exact (hS t).1
  have hpinv := fun t => preF_inv (K := K) (rt := rt) (cand := delivCand) (q := q)
    (act0 := act0) hG h0 hn t
  have heq : ∀ t, runS K rt delivV u q ⟨hr0, act0⟩ t = runH K rt delivV u q ⟨hr0, act0⟩ t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      show (relStepS K rt delivV (u (t + 1))
          (if q t = true then (qRetireH K rt (runS K rt delivV u q ⟨hr0, act0⟩ t)).1
            else runS K rt delivV u q ⟨hr0, act0⟩ t)).1
        = (relStepH K rt delivV (u (t + 1))
          (if q t = true then (qRetireH K rt (runH K rt delivV u q ⟨hr0, act0⟩ t)).1
            else runH K rt delivV u q ⟨hr0, act0⟩ t)).1
      rw [ih]
      exact (relStepS_spec delivV (hpre t) (hpinv t) (u (t + 1)) (hn t).1).1
  refine ⟨heq t, ?_⟩
  obtain ⟨_, c2, c3⟩ := relStepS_spec delivV (hpre t) (hpinv t) (u (t + 1)) (hn t).1
  obtain ⟨e1, e2, _⟩ := rstep_endpoints delivCand (u (t + 1))
    (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r
  have elo : (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.lo
      = (wave (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G (u (t + 1)).1
          (u (t + 1)).2.1 (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.lo).1 := e1
  have ehi : (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.hi
      = (wave (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G (u (t + 1)).1
          (u (t + 1)).2.2 (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.hi).1 := e2
  have hq2 : (if q t = true then K + (qRetireH K rt (runH K rt delivV u q ⟨hr0, act0⟩ t)).2
        else 0)
      = (if q t = true then K + (qRetire K rt
          (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2 else 0) := by
    rw [(qRetireH_sim K rt (hS t).1).2]
    rfl
  have hcS : costS K rt delivV u q ⟨hr0, act0⟩ t
      = (if q t = true then K + (qRetire K rt
          (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2 else 0)
        + (relStepS K rt delivV (u (t + 1))
            (if q t = true then (qRetireH K rt (runH K rt delivV u q ⟨hr0, act0⟩ t)).1
              else runH K rt delivV u q ⟨hr0, act0⟩ t)).2 := by
    unfold costS
    rw [heq t, hq2]
  have hcF : costF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
      = (if q t = true then K + (qRetire K rt
          (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2 else 0)
        + (relStep K rt delivCand (u (t + 1))
            (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2 := rfl
  have hvF : volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
      = vol (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G
          (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.lo
          (wave (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G (u (t + 1)).1
            (u (t + 1)).2.1 (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.lo).1
        + vol (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G
          (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.hi
          (wave (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G (u (t + 1)).1
            (u (t + 1)).2.2 (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.hi).1 := by
    unfold volF
    rw [elo, ehi]
  rw [hcS, hcF, hvF]
  constructor
  · have key : ∀ (X cs kv A : ℕ), cs + 4 * (G0.L + 3) ≤ 8 + 2 * kv + 2 * A →
        X + cs + 4 * (G0.L + 3) ≤ 8 + 2 * kv + 2 * (X + A) := by
      intros
      omega
    exact key _ _ _ _ c2
  · exact c3.trans (Nat.le_add_left _ _)

end EngineS

/-! ## The Graph-Eager engine on implemented heaps -/

section EngineE

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- State of the full-incidence engine on implemented heaps (lower and upper endpoint)
after `t` rollouts, with the sparse scheduler. -/
def runE (G : Dag) (u : ℕ → ℕ × α × α) (s0 : HEState α × HEState α) :
    ℕ → HEState α × HEState α
  | 0 => s0
  | t + 1 => ((waveS G (u (t + 1)).1 (u (t + 1)).2.1 (runE G u s0 t).1).1,
      (waveS G (u (t + 1)).1 (u (t + 1)).2.2 (runE G u s0 t).2).1)

/-- Computed cost of the full query of time `t` (if any: leader scan and stop scan over
all `K` actions) and of the two waves of rollout `t + 1`. -/
def costE (G : Dag) (K : ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool) (s0 : HEState α × HEState α)
    (t : ℕ) : ℕ :=
  (if q t = true then 2 * K else 0)
    + (waveS G (u (t + 1)).1 (u (t + 1)).2.1 (runE G u s0 t).1).2
    + (waveS G (u (t + 1)).1 (u (t + 1)).2.2 (runE G u s0 t).2).2

variable {G0 : Dag} {u : ℕ → ℕ × α × α} {lo0 hi0 : EState α}

/-- **Graph-Eager on implemented heaps.**  At every time the implemented full-incidence
engine represents the state of `CostEngines.runState`, and the cost of step `t` is between
the full-incidence deliveries `eagerPlus t` and
`2K·[query] + 8 + 2 (⌈log₂ D⌉ + 3 + κ) · eagerPlus t`. -/
theorem runE_spec (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (K : ℕ)
    (q : ℕ → Bool) (hl hu : HEState α) (sl : SimE G0 hl lo0) (su : SimE G0 hu hi0) (t : ℕ) :
    SimE G0 (runE G0 u (hl, hu) t).1 (runState G0 u (lo0, hi0) t).1 ∧
    SimE G0 (runE G0 u (hl, hu) t).2 (runState G0 u (lo0, hi0) t).2 ∧
    eagerPlus G0 u lo0 hi0 t ≤ costE G0 K u q (hl, hu) t ∧
    costE G0 K u q (hl, hu) t
      ≤ (if q t = true then 2 * K else 0) + 8
        + 2 * ((Nat.clog 2 D + 3 + kap G0) * eagerPlus G0 u lo0 hi0 t) := by
  have hsim : ∀ t, SimE G0 (runE G0 u (hl, hu) t).1 (runState G0 u (lo0, hi0) t).1 ∧
      SimE G0 (runE G0 u (hl, hu) t).2 (runState G0 u (lo0, hi0) t).2 := by
    intro t
    induction t with
    | zero => exact ⟨sl, su⟩
    | succ t ih =>
      obtain ⟨i1, i2, _, _⟩ := live_eq_eager (cand := noCand) hG h0 hn t
      obtain ⟨a, _, _, _⟩ := hn t
      obtain ⟨l1, _, _⟩ := waveS_spec hG (u (t + 1)).1 (u (t + 1)).2.1 _ _ a ih.1 i1
      obtain ⟨u1, _, _⟩ := waveS_spec hG (u (t + 1)).1 (u (t + 1)).2.2 _ _ a ih.2 i2
      constructor
      · show SimE G0 (waveS G0 (u (t + 1)).1 (u (t + 1)).2.1 (runE G0 u (hl, hu) t).1).1
          (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
        rw [l1]
        exact (HeapImpl.waveH_sim G0 _ _ _ _ ih.1).1
      · show SimE G0 (waveS G0 (u (t + 1)).1 (u (t + 1)).2.2 (runE G0 u (hl, hu) t).2).1
          (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1
        rw [u1]
        exact (HeapImpl.waveH_sim G0 _ _ _ _ ih.2).1
  refine ⟨(hsim t).1, (hsim t).2, ?_⟩
  obtain ⟨i1, i2, _, _⟩ := live_eq_eager (cand := noCand) hG h0 hn t
  obtain ⟨a, _, _, _⟩ := hn t
  obtain ⟨_, l2, l3⟩ := waveS_spec hG (u (t + 1)).1 (u (t + 1)).2.1 _ _ a (hsim t).1 i1
  obtain ⟨_, u2, u3⟩ := waveS_spec hG (u (t + 1)).1 (u (t + 1)).2.2 _ _ a (hsim t).2 i2
  have bl := (chgSum_bounds D hD (runState G0 u (lo0, hi0) t).1
    (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1).2
  have bh := (chgSum_bounds D hD (runState G0 u (lo0, hi0) t).2
    (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1).2
  have hp : eagerPlus G0 u lo0 hi0 t
      = vol G0 (runState G0 u (lo0, hi0) t).1
          (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
        + vol G0 (runState G0 u (lo0, hi0) t).2
          (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1 := rfl
  have hexp : (Nat.clog 2 D + 3 + kap G0)
        * (vol G0 (runState G0 u (lo0, hi0) t).1
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
          + vol G0 (runState G0 u (lo0, hi0) t).2
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1)
      = (Nat.clog 2 D + 3) * vol G0 (runState G0 u (lo0, hi0) t).1
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
        + kap G0 * vol G0 (runState G0 u (lo0, hi0) t).1
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
        + ((Nat.clog 2 D + 3) * vol G0 (runState G0 u (lo0, hi0) t).2
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1
          + kap G0 * vol G0 (runState G0 u (lo0, hi0) t).2
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1) := by
    ring
  rw [hp, hexp]
  unfold costE
  constructor
  · omega
  · omega

end EngineE

/-! ## A trajectory and the assembled statement -/

section Final

/-- **A coupled trajectory**: a circuit `G0` of maximum degree `D` with duplicate-free
child lists, its internal gates `order` listed by nondecreasing level, initial terminal
intervals (`hl.val`, `hu.val` at the leaves) with empty heaps, nested terminal updates `u`,
`T` rollouts, root queries at the times `t < T` with `q t`, `K ≥ 1` root actions with gates
`rt i`, the comparison map `φ` and tolerance `ε ≥ 0` of the stopping bit, and a passive
traversal policy: rollout `t` starts at `start t` and follows `pick t`. -/
structure Traj (α : Type*) [LinearOrder α] [OrderBot α] where
  G0 : Dag
  D : ℕ
  order : List ℕ
  hl : HEState α
  hu : HEState α
  u : ℕ → ℕ × α × α
  q : ℕ → Bool
  T : ℕ
  K : ℕ
  rt : ℕ → ℕ
  φ : α → ℝ
  ε : ℝ
  start : ℕ → ℕ
  pick : ℕ → ℕ → ℕ
  wf : G0.WF
  deg : ∀ p, (G0.children p).length ≤ D
  nodup : ∀ g, (G0.children g).Nodup
  order_all : ∀ g, G0.children g ≠ [] → g ∈ order
  order_int : ∀ g ∈ order, G0.children g ≠ []
  order_sorted : order.Pairwise (fun a b => G0.level a ≤ G0.level b)
  order_nodup : order.Nodup
  empty_lo : ∀ p, hl.hp p = Heap.empty
  empty_hi : ∀ p, hu.hp p = Heap.empty
  leaf : ∀ g, G0.children g = [] → hl.val g ≤ hu.val g
  nested : NestedRun G0 noCand u
    ⟨G0, (initPass G0 order ⟨hl.val, fun _ _ => ⊥⟩).1, (initPass G0 order ⟨hu.val, fun _ _ => ⊥⟩).1⟩
  hK : 0 < K
  hφ : StrictMono φ
  hε : 0 ≤ ε
  pick_mem : ∀ t v, G0.children v ≠ [] → pick t v ∈ G0.children v

namespace Traj

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : Traj α)

/-- The initialised lower-endpoint state in the model of `DagRetire.lean`. -/
def lo0 : EState α := (initPass R.G0 R.order ⟨R.hl.val, fun _ _ => ⊥⟩).1

/-- The initialised upper-endpoint state in the model of `DagRetire.lean`. -/
def hi0 : EState α := (initPass R.G0 R.order ⟨R.hu.val, fun _ _ => ⊥⟩).1

/-- The initialised lower-endpoint state on implemented heaps. -/
def hlo : HEState α := (initPassH R.G0 R.order R.hl).1

/-- The initialised upper-endpoint state on implemented heaps. -/
def hhi : HEState α := (initPassH R.G0 R.order R.hu).1

/-- Computed cost of the initialisation (both endpoints, `EngineFinal.initPassH`). -/
def initW : ℕ := (initPassH R.G0 R.order R.hl).2 + (initPassH R.G0 R.order R.hu).2

/-- Sampler work: the `T` traversals of the original circuit. -/
def samp : ℕ := ∑ t ∈ range R.T, (walk R.G0 (R.pick t) (R.G0.L + 1) (R.start t)).2

/-- Number of root queries `Q`. -/
def Q : ℕ := ((range R.T).filter (fun t => R.q t = true)).card

/-- Full-incidence changed-endpoint deliveries `S₀`. -/
def S0 : ℕ := ∑ t ∈ range R.T, eagerPlus R.G0 R.u R.lo0 R.hi0 t

/-- Live deliveries `S` of the Graph-Selective engine. -/
def S : ℕ := ∑ t ∈ range R.T,
  volF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t

/-- Permanent retirements `R` of internal incidences. -/
def Rret : ℕ := ∑ t ∈ range R.T,
  retF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t

/-- **`W_eager`**: computed initialisation, sampler, and the `T` steps of the
full-incidence engine on implemented heaps. -/
def Weager : ℕ :=
  R.initW + R.samp + ∑ t ∈ range R.T, costE R.G0 R.K R.u R.q (R.hlo, R.hhi) t

/-- **`W_live`**: computed initialisation, sampler, and the `T` steps of the
Graph-Selective engine on implemented heaps. -/
def Wlive : ℕ :=
  R.initW + R.samp
    + ∑ t ∈ range R.T, costS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t

/-- Leader-and-stop output of the implemented full-incidence engine at time `t`
(all actions are scanned). -/
noncomputable def outE (t : ℕ) : Option ℕ × Bool :=
  qOut R.φ R.ε R.K (fun i => (runE R.G0 R.u (R.hlo, R.hhi) t).1.val (R.rt i))
    (fun i => (runE R.G0 R.u (R.hlo, R.hhi) t).2.val (R.rt i)) (fun _ => true)

/-- Leader-and-stop output of the implemented Graph-Selective engine at time `t`
(only the active actions are scanned). -/
noncomputable def outS (t : ℕ) : Option ℕ × Bool :=
  qOut R.φ R.ε R.K
    (fun i => (runS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t).r.lo.val
      (R.rt i))
    (fun i => (runS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t).r.hi.val
      (R.rt i))
    (runS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t).act

/-- **Costed initialisation** (`eq:ram-work-bounds`, the term `|V| + |E|`).  The
initialisation program produces implemented states representing states that satisfy the
engine invariant, at computed cost at most `4 (|V| + (⌈log₂ D⌉ + 1) |E|)`. -/
theorem init_spec :
    SimE R.G0 R.hlo R.lo0 ∧ SimE R.G0 R.hhi R.hi0 ∧ RInv R.G0 ⟨R.G0, R.lo0, R.hi0⟩ ∧
    R.initW ≤ 4 * (R.G0.N + (Nat.clog 2 R.D + 1) * live R.G0) := by
  obtain ⟨i1, i2⟩ := init_engine R.wf R.order (⟨R.hl.val, fun _ _ => ⊥⟩ : EState α)
    ⟨R.hu.val, fun _ _ => ⊥⟩ R.order_all R.order_int R.order_sorted R.leaf
  obtain ⟨l1, l2⟩ := initPassH_sim (G := R.G0) R.order R.hl ⟨R.hl.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_lo
  obtain ⟨u1, u2⟩ := initPassH_sim (G := R.G0) R.order R.hu ⟨R.hu.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_hi
  have hinit := initCost_sum_le R.G0 R.D R.deg R.order
  have hmemN : ∀ g ∈ R.order, g < R.G0.N := by
    intro g hg
    obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (R.order_int g hg)
    exact R.wf.parent_lt c g ((R.wf.parents_iff c g).2 hc)
  have hdeg : (R.order.map (fun g => (R.G0.children g).length)).sum ≤ live R.G0 := by
    rw [← List.sum_toFinset _ R.order_nodup]
    unfold live
    apply sum_le_sum_of_subset
    intro g hg
    rw [List.mem_toFinset] at hg
    exact mem_range.2 (hmemN g hg)
  have hlen : R.order.length ≤ R.G0.N := by
    rw [← List.toFinset_card_of_nodup R.order_nodup]
    have : R.order.toFinset ⊆ range R.G0.N := by
      intro g hg
      rw [List.mem_toFinset] at hg
      exact mem_range.2 (hmemN g hg)
    have := card_le_card this
    rwa [card_range] at this
  have hmul := Nat.mul_le_mul_left (Nat.clog 2 R.D + 1) hdeg
  refine ⟨l1, u1, i1, ?_⟩
  unfold initW
  omega

/-- **Sampler work** (`eq:ram-work-bounds`, the term `T`): between `T` and
`T (L + 1)(D + 1)`. -/
theorem samp_bounds : R.T ≤ R.samp ∧ R.samp ≤ R.T * ((R.G0.L + 1) * (R.D + 1)) := by
  have h : ∀ t, 1 ≤ (walk R.G0 (R.pick t) (R.G0.L + 1) (R.start t)).2 ∧
      (walk R.G0 (R.pick t) (R.G0.L + 1) (R.start t)).2 ≤ (R.G0.L + 1) * (R.D + 1) := by
    intro t
    have hl := R.wf.level_le (R.start t)
    obtain ⟨_, w2, w3⟩ := walk_spec R.wf R.D R.deg (R.pick t) (R.pick_mem t) (R.G0.L + 1)
      (R.start t) (by omega)
    exact ⟨w2, w3.trans (Nat.mul_le_mul_right _ (by omega))⟩
  unfold samp
  constructor
  · calc R.T = ∑ _t ∈ range R.T, 1 := by simp
      _ ≤ _ := sum_le_sum (fun t _ => (h t).1)
  · calc ∑ t ∈ range R.T, (walk R.G0 (R.pick t) (R.G0.L + 1) (R.start t)).2
        ≤ ∑ _t ∈ range R.T, (R.G0.L + 1) * (R.D + 1) := sum_le_sum (fun t _ => (h t).2)
      _ = R.T * ((R.G0.L + 1) * (R.D + 1)) := by simp

/-- **`prop:uct-coupling` with `eq:ram-work-bounds`: the assembled statement.**

For a coupled trajectory `R` with `T` rollouts, `Q` root queries, `K ≥ 1` root actions,
maximum degree `D`, `S₀` full-incidence deliveries, `S` live deliveries and `R` permanent
retirements, with initialisation, both engines and all heap operations executed by the
implemented programs:

1. the Graph-Selective engine (active actions only) and the Graph-Eager engine (all
   actions) return the same leader and the same stopping bit at every time;
2. `T + S₀ ≤ W_eager` (message-volume lower bound) and
   `W_eager ≤ initW + samp + 8T + 2QK + 2 (⌈log₂ D⌉ + 3 + κ) S₀`;
3. `T + S ≤ W_live` and
   `W_live ≤ initW + samp + 8T + 8QK + 2 (⌈log₂ D⌉ + 5 + κ) S + 2 (2⌈log₂ D⌉ + 4) R
      + 4 (|V| + |E|)`;
4. `initW ≤ 4 (|V| + (⌈log₂ D⌉ + 1) |E|)`, `T ≤ samp ≤ T (L + 1)(D + 1)`, `S ≤ S₀`,
   `R ≤ |E|`.

Here `κ = kap G0 = ⌈log₂ (L + 1)⌉ + 3`.  No free parameter remains. -/
theorem _root_.JointRootCert.LiteralE4.ram_work_bounds_literal :
    (∀ t, R.outS t = R.outE t) ∧
    (R.T + R.S0 ≤ R.Weager) ∧
    (R.Weager ≤ R.initW + R.samp + 8 * R.T + 2 * (R.Q * R.K)
      + 2 * ((Nat.clog 2 R.D + 3 + kap R.G0) * R.S0)) ∧
    (R.T + R.S ≤ R.Wlive) ∧
    (R.Wlive ≤ R.initW + R.samp + 8 * R.T + 8 * (R.Q * R.K)
      + 2 * ((Nat.clog 2 R.D + 5 + kap R.G0) * R.S)
      + 2 * ((2 * Nat.clog 2 R.D + 4) * R.Rret) + 4 * (R.G0.N + live R.G0)) ∧
    (R.initW ≤ 4 * (R.G0.N + (Nat.clog 2 R.D + 1) * live R.G0)) ∧
    (R.T ≤ R.samp ∧ R.samp ≤ R.T * ((R.G0.L + 1) * (R.D + 1))) ∧
    (R.S ≤ R.S0) ∧ (R.Rret ≤ live R.G0) := by
  obtain ⟨sl, su, h0, hinit⟩ := R.init_spec
  have hn : NestedRun R.G0 noCand R.u ⟨R.G0, R.lo0, R.hi0⟩ := R.nested
  have hsimR : SimR (⟨R.G0, R.hlo, R.hhi⟩ : HRState α) ⟨R.G0, R.lo0, R.hi0⟩ := ⟨rfl, sl, su⟩
  obtain ⟨sa, sb⟩ := R.samp_bounds
  have hE := fun t => runE_spec R.wf R.D R.deg h0 hn R.K R.q R.hlo R.hhi sl su t
  have hSp := fun t => runS_spec (K := R.K) (rt := R.rt) R.wf h0 hn R.q
    (⟨R.G0, R.hlo, R.hhi⟩ : HRState α) hsimR (fun _ => true) t
  obtain ⟨b1, _⟩ := ram_work_bounds_impl (K := R.K) (rt := R.rt) R.wf R.D R.deg h0 hn R.hK
    R.φ R.hφ R.ε R.hε R.q R.T 0 (⟨R.G0, R.hlo, R.hhi⟩ : HRState α) hsimR
  obtain ⟨_, _, _, _, f5, f6, f7⟩ := ram_work_bounds_final R.wf R.D R.deg h0 hn R.hK R.rt
    R.φ R.hφ R.ε R.hε R.q R.T 0
  -- sums over the steps
  have hEl : ∑ t ∈ range R.T, eagerPlus R.G0 R.u R.lo0 R.hi0 t
      ≤ ∑ t ∈ range R.T, costE R.G0 R.K R.u R.q (R.hlo, R.hhi) t :=
    sum_le_sum (fun t _ => (hE t).2.2.1)
  have hEu : ∑ t ∈ range R.T, costE R.G0 R.K R.u R.q (R.hlo, R.hhi) t
      ≤ 2 * (R.Q * R.K) + 8 * R.T
        + 2 * ((Nat.clog 2 R.D + 3 + kap R.G0)
          * ∑ t ∈ range R.T, eagerPlus R.G0 R.u R.lo0 R.hi0 t) := by
    calc ∑ t ∈ range R.T, costE R.G0 R.K R.u R.q (R.hlo, R.hhi) t
        ≤ ∑ t ∈ range R.T, ((if R.q t = true then 2 * R.K else 0) + 8
          + 2 * ((Nat.clog 2 R.D + 3 + kap R.G0) * eagerPlus R.G0 R.u R.lo0 R.hi0 t)) :=
          sum_le_sum (fun t _ => (hE t).2.2.2)
      _ = 2 * (R.Q * R.K) + 8 * R.T
          + 2 * ((Nat.clog 2 R.D + 3 + kap R.G0)
            * ∑ t ∈ range R.T, eagerPlus R.G0 R.u R.lo0 R.hi0 t) := by
          rw [sum_add_distrib, sum_add_distrib, ← sum_filter, sum_const, sum_const, card_range,
            ← mul_sum, ← mul_sum, smul_eq_mul, smul_eq_mul]
          unfold Q
          ring
  have hSl : ∑ t ∈ range R.T,
        volF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t
      ≤ ∑ t ∈ range R.T,
        costS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t :=
    sum_le_sum (fun t _ => (hSp t).2.2)
  have hSu : ∑ t ∈ range R.T,
        costS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t
        + R.T * (4 * (R.G0.L + 3))
      ≤ 8 * R.T
        + 2 * (kap R.G0 * ∑ t ∈ range R.T,
          volF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t)
        + 2 * ∑ t ∈ range R.T,
          costF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t := by
    calc ∑ t ∈ range R.T,
          costS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t
          + R.T * (4 * (R.G0.L + 3))
        = ∑ t ∈ range R.T,
          (costS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t
            + 4 * (R.G0.L + 3)) := by
          rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
      _ ≤ ∑ t ∈ range R.T, (8
          + 2 * (kap R.G0
            * volF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t)
          + 2 * costF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t) :=
          sum_le_sum (fun t _ => (hSp t).2.1)
      _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, ← mul_sum, ← mul_sum,
            ← mul_sum, smul_eq_mul]
          ring
  have hTL : R.T * (4 * (R.G0.L + 3)) = 2 * (2 * R.T * (R.G0.L + 3)) := by ring
  have hQK : ((range R.T).filter (fun t => R.q t = true)).card * (4 * R.K)
      = 4 * (R.Q * R.K) := by
    unfold Q
    ring
  have hx1 : (Nat.clog 2 R.D + 5 + kap R.G0) * R.S
      = (Nat.clog 2 R.D + 5) * R.S + kap R.G0 * R.S := Nat.add_mul _ _ _
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, hinit, ⟨sa, sb⟩, f6, f7⟩
  · unfold outS outE
    rw [(hSp t).1, b1 t, (hE t).1.val, (hE t).2.1.val]
  · unfold Weager S0
    omega
  · unfold Weager S0
    omega
  · unfold Wlive S
    omega
  · rw [hx1]
    unfold Wlive S Rret
    rw [hQK] at f5
    rw [hTL] at hSu
    omega

/-- **Completeness of the release cascade in the implemented Graph-Selective engine.**
If initially every parentless internal gate of `G0` is the gate of a root action, then at
every time every gate of the engine's live circuit that still has live children is
reachable through live incidences from the gate of an active root action
(`LiteralE4a.runF_live_anchored`, transported along `runS = runH ≃ runF`).  Hence every
gate not so reachable has been released. -/
theorem _root_.JointRootCert.LiteralE4.ram_cascade_complete
    (hof : ∀ g, ¬ Orphan (protOf R.K R.rt (fun _ => true)) R.G0 g) (t g : ℕ)
    (hg : (runS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t).r.G.children g
      ≠ []) :
    Anch (protOf R.K R.rt
        (runS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t).act)
      (runS R.K R.rt delivV R.u R.q ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩ t).r.G g := by
  obtain ⟨sl, su, h0, -⟩ := R.init_spec
  have hsimR : SimR (⟨R.G0, R.hlo, R.hhi⟩ : HRState α) ⟨R.G0, R.lo0, R.hi0⟩ := ⟨rfl, sl, su⟩
  have e1 := (runS_spec (K := R.K) (rt := R.rt) R.wf h0 R.nested R.q _ hsimR
    (fun _ => true) t).1
  have hS := (runH_sim (K := R.K) (rt := R.rt) delivV R.u R.q
    (hs0 := ⟨⟨R.G0, R.hlo, R.hhi⟩, fun _ => true⟩)
    (s0 := ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩) ⟨hsimR, rfl⟩ t).1
  rw [e1] at hg ⊢
  rw [hS.r.G] at hg ⊢
  rw [hS.act]
  exact runF_live_anchored R.wf h0 R.nested hof t g hg

end Traj

end Final

end LiteralE4
end JointRootCert
