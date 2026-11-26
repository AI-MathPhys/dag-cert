/-
Joint Root Certification: `thm:coded-covers`, upper half, for BOTH monitors
("Graph Eager" and "Graph Selective") on the parity-grid DAG.

Manuscript result covered:

* `thm:coded-covers` (Every-Layout Dyadic Cover Lower Bound; also `thm:coded-main`), the
  sentence "TA-UCT with `c = 2` stops within `O(r² log² r)` total scalar work under either
  Graph Eager or Graph Selective and certifies the optimal action with probability at
  least `1 - δ`" (Step 3 of the proof).

`ParityGrid.coded_main` proves this for the eager interval engine only.  Here the
Graph-Selective engine of `RetireFinal.lean` (`runF`: strict-dominance retirement of
incidences with the delivery policy `delivCand`, release of orphaned gates, root-action
retirement at queries, the leader-and-stop query `qOut`) is instantiated on `pgDag k` with
the SAME terminal updates `pgUpd` that `coded_main` feeds to the eager engine, with a root
query after every rollout and with the `d + 1` root actions `pgGate` as root gates.

Main statements.

* `pg_nested`: on the coverage event the updates `pgUpd` form a `DagRetire.NestedRun`
  (nested by `tape_box_nested`; nonempty because the true mean lies in every box).  OFF the
  coverage event the Hoeffding boxes can become empty and the update sequence need not be
  nested; nothing is claimed there (the theorem is a "with probability at least `1 - δ`"
  statement, and the confidence alarm that the manuscript invokes off the event is not
  modelled).
* `qSel_eq_qEag`: the selective monitor's leader-and-stop output equals the eager one at
  every time.
* `qEag_iff`: the eager output is `(some a, true)` iff `ParityGrid.pgStops … a`, so the
  stopping time is the one of `coded_main`.
* `selCost_sum_le`, `selWork_le`: the work of the selective monitor.
* `parity_certified_both` (pathwise) and `coded_covers_selective` (probabilistic, the full
  statement of `thm:coded-covers` with both monitors).

Work of the selective monitor up to the stopping time `τ` (`selWork`):

* computed by the engine (`RetireFinal.costF`, with the charged heap primitive of
  `CostEngines.lean`): the waves on the live circuit, the retirement tests and
  retirements, the release cascades, and at each of the times `0, …, τ - 1` a query (stop
  scan, leader scan, root-retirement scan and its release cascade);
* charged by definition, exactly as in `ParityGrid.pgWork`: `pgInitCost` (initialisation),
  `pgRolloutCost` per rollout (allocator and terminal table) and `pgQueryCost = 2 (d + 1)`
  for the final leader-and-stop query at time `τ`.
-/
import JointRootCert.RetireFinal
import JointRootCert.ParityGrid

namespace JointRootCert
namespace LiteralK2

open Finset MeasureTheory CostEngines DagRetire EngineFinal RetireFinal ParityGrid
  _root_.JointRootCert.Representation

noncomputable section

/-! ## Deliveries of one wave on a three-layer circuit -/

section Vol

variable {α : Type*} [LinearOrder α] [OrderBot α] {G : Dag}

/-- Number of deliveries of one wave on a circuit of parity-grid shape (the count inside
`CostEngines.wave_cost_three_layers`, without the heap factor). -/
theorem vol_three_layers (hG : G.WF) (x : ℕ) (y : α) (s0 : EState α) (hx : x < G.N)
    (h0 : Inv G s0) (m0 m1 m2 : ℕ)
    (hm0 : (G.parents x).length ≤ m0)
    (hm1 : ∀ g ∈ G.parents x, (G.parents g).length ≤ m1)
    (hm2 : ∀ g ∈ (G.parents x).flatMap G.parents, (G.parents g).length ≤ m2)
    (hm3 : ∀ g ∈ ((G.parents x).flatMap G.parents).flatMap G.parents, G.parents g = []) :
    vol G s0 (wave G x y s0).1 ≤ m0 + m0 * m1 + m0 * m1 * m2 := by
  have hclosed : ∀ g ∈ ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents).toFinset,
      ∀ p ∈ G.parents g, p ∈ ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents).toFinset := by
    intro g hg p hp
    simp only [List.mem_toFinset, List.mem_append, List.mem_singleton] at hg ⊢
    rcases hg with ((rfl | hg) | hg) | hg
    · exact Or.inl (Or.inl (Or.inr hp))
    · exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨g, hg, hp⟩))
    · exact Or.inr (List.mem_flatMap.2 ⟨g, hg, hp⟩)
    · rw [hm3 g hg] at hp
      simp at hp
  have hxT : x ∈ ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents).toFinset := by simp
  have hvol := vol_le_of_closed hG x y s0 hx h0 _ hxT hclosed
  have hlist := sum_toFinset_le ([x] ++ G.parents x ++ (G.parents x).flatMap G.parents
        ++ ((G.parents x).flatMap G.parents).flatMap G.parents)
      (fun g => (G.parents g).length)
  have e1 : ((G.parents x).map (fun g => (G.parents g).length)).sum
      = ((G.parents x).flatMap G.parents).length := by
    rw [List.length_flatMap]
  have e2 : (((G.parents x).flatMap G.parents).map (fun g => (G.parents g).length)).sum
      = (((G.parents x).flatMap G.parents).flatMap G.parents).length := by
    rw [List.length_flatMap]
  have e3 : ((((G.parents x).flatMap G.parents).flatMap G.parents).map
      (fun g => (G.parents g).length)).sum = 0 := by
    have := flatMap_length_le (((G.parents x).flatMap G.parents).flatMap G.parents)
      G.parents 0 (fun g hg => by rw [hm3 g hg]; simp)
    rw [List.length_flatMap] at this
    omega
  have b2 := flatMap_length_le (G.parents x) G.parents m1 hm1
  have b3 := flatMap_length_le ((G.parents x).flatMap G.parents) G.parents m2 hm2
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, e1, e2, e3] at hlist
  have b2' : ((G.parents x).flatMap G.parents).length ≤ m0 * m1 :=
    b2.trans (Nat.mul_le_mul_right _ hm0)
  have b3' : (((G.parents x).flatMap G.parents).flatMap G.parents).length ≤ m0 * m1 * m2 :=
    b3.trans (Nat.mul_le_mul_right _ b2')
  omega

end Vol

/-! ## The leader-and-stop query with all actions active is the canonical stopping test -/

section Query

/-- The order embedding of the engine's values into the reals. -/
def cR : NNReal → ℝ := fun y => (y : ℝ)

lemma cR_strictMono : StrictMono cR := fun _ _ h => NNReal.coe_lt_coe.2 h

/-- With all `K` actions active, the query returns `(some a, true)` exactly when `a` is the
canonical (lowest-index) lower-bound leader and the marginal stopping test passes. -/
lemma qOut_all_iff (K : ℕ) (L U : ℕ → NNReal) (ε : ℝ) (a : Fin K) :
    qOut cR ε K L U (fun _ => true) = (some (a : ℕ), true)
      ↔ MarginalStops univ (fun b : Fin K => ((L b : NNReal) : ℝ))
          (fun b : Fin K => ((U b : NNReal) : ℝ)) ε a := by
  unfold qOut
  constructor
  · intro h
    have h1 : leadScan L (fun _ => true) K = some (a : ℕ) := congrArg Prod.fst h
    have h2 : stopScan cR ε U (L a) a (fun _ => true) K = true := by
      have := congrArg Prod.snd h
      rw [h1] at this
      exact this
    obtain ⟨_, _, hsp⟩ := (leadScan_spec L (fun _ => true) K).2 a h1
    refine ⟨⟨mem_univ _, fun b _ => NNReal.coe_le_coe.2 (hsp b b.isLt rfl).1,
      fun b _ hb => Fin.le_def.2 ((hsp b b.isLt rfl).2 (NNReal.coe_injective hb))⟩,
      fun b _ hba => ?_⟩
    exact (stopScan_spec cR ε U (L a) a (fun _ => true) K).1 h2 b b.isLt rfl
      (fun e => hba (Fin.ext e))
  · rintro ⟨⟨_, hmax, hlow⟩, hst⟩
    cases hl : leadScan L (fun _ => true) K with
    | none =>
      have := (leadScan_spec L (fun _ => true) K).1 hl a a.isLt
      simp at this
    | some a' =>
      obtain ⟨ha'K, _, hsp⟩ := (leadScan_spec L (fun _ => true) K).2 a' hl
      have h1 := hsp a a.isLt rfl
      have h2 : ((L a' : NNReal) : ℝ) ≤ L a := hmax ⟨a', ha'K⟩ (mem_univ _)
      have heq : L a = L a' := le_antisymm h1.1 (NNReal.coe_le_coe.1 h2)
      have h4 := h1.2 heq
      have h5 : (a : ℕ) ≤ a' := Fin.le_def.1 (hlow ⟨a', ha'K⟩ (mem_univ _)
        (by show ((L a' : NNReal) : ℝ) = L a; rw [heq]))
      obtain rfl : a' = (a : ℕ) := by omega
      have hb : stopScan cR ε U (L a) a (fun _ => true) K = true :=
        (stopScan_spec cR ε U (L a) a (fun _ => true) K).2
          (fun i hi _ hia => hst ⟨i, hi⟩ (mem_univ _) (fun e => hia (congrArg Fin.val e)))
      show (some (a : ℕ), stopScan cR ε U (L a) a (fun _ => true) K) = _
      rw [hb]

/-- If the stop bit of a query is set, the query names a leader `a < K`. -/
lemma qOut_stop (K : ℕ) (L U : ℕ → NNReal) (ε : ℝ) (act : ℕ → Bool)
    (h : (qOut cR ε K L U act).2 = true) :
    ∃ a : Fin K, qOut cR ε K L U act = (some (a : ℕ), true) := by
  unfold qOut at h ⊢
  cases hl : leadScan L act K with
  | none =>
    rw [hl] at h
    exact absurd h (by simp)
  | some a =>
    rw [hl] at h
    exact ⟨⟨a, ((leadScan_spec L act K).2 a hl).1⟩, Prod.ext rfl h⟩

end Query

/-! ## The two monitors on the parity grid -/

section Monitors

variable {k : ℕ}

/-- Gate of root action `i` (`i < d + 1`): the parity-action gate, or the terminal `w*`. -/
def pgRt (k : ℕ) (i : ℕ) : ℕ := if h : i < pgD k + 1 then gid (pgGate k ⟨i, h⟩) else 0

lemma pgRt_fin (a : Fin (pgD k + 1)) : pgRt k a = gid (pgGate k a) := by
  unfold pgRt
  rw [dite_eq_left a.isLt]

/-- Initial state of both engines: all incidences live, every interval `[0, 1]`. -/
lemma pg_h0 (k : ℕ) : RInv (pgDag k) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ :=
  RInv.init pgDag_wf pgInit_inv.1 pgInit_inv.2 (fun _ _ => show (⊥ : NNReal) ≤ 1 from bot_le)

variable {x : GridTerminal k → ℕ → ℝ} {zt : ℕ → GridTerminal k} {δ : ℝ}

/-- **Reference run on the coverage event.**  The engine without retirement keeps its
invariant and its terminal gates store the Hoeffding boxes. -/
theorem pg_ref (hx : PGTape x) {m : GridTerminal k → ℝ}
    (hcov : tapeCovered (pgM k) δ x zt m) : ∀ t,
    RInv (pgDag k) (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t) ∧
    ∀ z, (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t).lo.val
          (gid (vT z)) = (pgTab δ x zt t z).1 ∧
      (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t).hi.val
          (gid (vT z)) = (pgTab δ x zt t z).2 := by
  intro t
  induction t with
  | zero =>
    obtain ⟨l1, l2, _, _⟩ := pgState_leaves hx δ zt 0
    exact ⟨pg_h0 k, fun z => ⟨l1 z, l2 z⟩⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hu := pgUpd_succ δ x zt t
    have hxN : gid (vT (zt t)) < (pgDag k).N := gid_lt _
    have hnest := tape_box_nested (pgM k) δ x zt t (zt t)
    have hc := hcov (t + 1)
    have h1 : (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t).lo.val
        (gid (vT (zt t))) ≤ (pgTab δ x zt (t + 1) (zt t)).1 := by
      rw [(ih2 (zt t)).1]
      exact Real.toNNReal_le_toNNReal hnest.1
    have h2 : (pgTab δ x zt (t + 1) (zt t)).1 ≤ (pgTab δ x zt (t + 1) (zt t)).2 :=
      Real.toNNReal_le_toNNReal ((hc.1 (zt t)).trans (hc.2 (zt t)))
    have h3 : (pgTab δ x zt (t + 1) (zt t)).2
        ≤ (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t).hi.val
          (gid (vT (zt t))) := by
      rw [(ih2 (zt t)).2]
      exact Real.toNNReal_le_toNNReal hnest.2
    have hw := waveStep_inv ih1
      (gid (vT (zt t)), (pgTab δ x zt (t + 1) (zt t)).1, (pgTab δ x zt (t + 1) (zt t)).2)
      hxN h1 h2 h3
    have e : rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ (t + 1)
        = (waveStep (gid (vT (zt t)), (pgTab δ x zt (t + 1) (zt t)).1,
              (pgTab δ x zt (t + 1) (zt t)).2)
            (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t)).1 := by
      rw [← hu]
      rfl
    obtain ⟨_, l2, l3, _⟩ := wave_spec ih1.wf (gid (vT (zt t)))
      (pgTab δ x zt (t + 1) (zt t)).1 _ (ih1.nEq ▸ hxN) ih1.invLo
    obtain ⟨_, u2, u3, _⟩ := wave_spec ih1.wf (gid (vT (zt t)))
      (pgTab δ x zt (t + 1) (zt t)).2 _ (ih1.nEq ▸ hxN) ih1.invHi
    refine ⟨e ▸ hw, fun z => ?_⟩
    have hls : (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t).G.children
        (gid (vT z)) = [] := (ih1.leaf_iff _).2 (children_term z)
    rw [e]
    by_cases hz : z = zt t
    · rw [hz] at hls ⊢
      exact ⟨l2 hls, u2 hls⟩
    · have hne : gid (vT z) ≠ gid (vT (zt t)) :=
        fun h => hz (Sum.inl_injective (gid_injective h))
      have et := pgTab_succ_of_ne δ x zt t hz
      exact ⟨(l3 _ hls hne).trans (((ih2 z).1).trans (by rw [et])),
        (u3 _ hls hne).trans (((ih2 z).2).trans (by rw [et]))⟩

/-- **Nestedness on the coverage event.**  If the means `m` lie in the Hoeffding boxes at
every time, the terminal updates `pgUpd` are nested with nonempty intervals. -/
theorem pg_nested (hx : PGTape x) {m : GridTerminal k → ℝ}
    (hcov : tapeCovered (pgM k) δ x zt m) :
    NestedRun (pgDag k) noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ := by
  intro t
  obtain ⟨_, ih2⟩ := pg_ref hx hcov t
  have hnest := tape_box_nested (pgM k) δ x zt t (zt t)
  have hc := hcov (t + 1)
  rw [pgUpd_succ]
  refine ⟨gid_lt _, ?_, ?_, ?_⟩
  · show (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t).lo.val
        (gid (vT (zt t))) ≤ (pgTab δ x zt (t + 1) (zt t)).1
    rw [(ih2 (zt t)).1]
    exact Real.toNNReal_le_toNNReal hnest.1
  · exact Real.toNNReal_le_toNNReal ((hc.1 (zt t)).trans (hc.2 (zt t)))
  · show (pgTab δ x zt (t + 1) (zt t)).2
        ≤ (rrun noCand (pgUpd δ x zt) ⟨pgDag k, (pgInit k).1, (pgInit k).2⟩ t).hi.val
          (gid (vT (zt t)))
    rw [(ih2 (zt t)).2]
    exact Real.toNNReal_le_toNNReal hnest.2

/-- State of the **Graph-Selective** monitor after `t` rollouts: `RetireFinal.runF` on
`pgDag k` with the delivery retirement policy, the updates `pgUpd`, a query with root
retirement after every rollout, and the `d + 1` root actions. -/
def selState (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    QS NNReal :=
  runF (pgD k + 1) (pgRt k) delivCand (pgUpd δ x zt) (fun _ => true)
    ⟨⟨pgDag k, (pgInit k).1, (pgInit k).2⟩, fun _ => true⟩ t

/-- Leader-and-stop output of the Graph-Selective monitor after `t` rollouts (it reads the
stored values of the active root actions only), at `ε = 1/5`. -/
def qSel (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    Option ℕ × Bool :=
  qOut cR (1 / 5) (pgD k + 1) (fun i => (selState δ x zt t).r.lo.val (pgRt k i))
    (fun i => (selState δ x zt t).r.hi.val (pgRt k i)) (selState δ x zt t).act

/-- Leader-and-stop output of the Graph-Eager monitor (the engine state `pgState` of
`ParityGrid.coded_main`, all root actions scanned) after `t` rollouts, at `ε = 1/5`. -/
def qEag (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    Option ℕ × Bool :=
  qOut cR (1 / 5) (pgD k + 1) (fun i => (pgState δ x zt t).1.val (pgRt k i))
    (fun i => (pgState δ x zt t).2.val (pgRt k i)) (fun _ => true)

/-- **The eager query is the stopping test of `coded_main`.**  It returns `(some a, true)`
exactly when `pgStops … a` holds. -/
theorem qEag_iff (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (a : Fin (pgD k + 1)) :
    qEag δ x zt t = (some (a : ℕ), true) ↔ pgStops δ x zt t a := by
  have eL : pgL δ x zt t
      = fun b : Fin (pgD k + 1) => (((pgState δ x zt t).1.val (pgRt k b) : NNReal) : ℝ) := by
    funext b
    rw [pgRt_fin]
    rfl
  have eU : pgU δ x zt t
      = fun b : Fin (pgD k + 1) => (((pgState δ x zt t).2.val (pgRt k b) : NNReal) : ℝ) := by
    funext b
    rw [pgRt_fin]
    rfl
  unfold pgStops qEag
  rw [eL, eU]
  exact qOut_all_iff (pgD k + 1) _ _ (1 / 5) a

/-- **Coupling of the two monitors** (`RetireFinal.ram_work_bounds_final`, part 1, i.e.
`query_coupling` with `live_eq_eager`).  On the coverage event the Graph-Selective monitor
returns the same leader and the same stopping bit as the Graph-Eager monitor after every
rollout. -/
theorem qSel_eq_qEag (hx : PGTape x) {m : GridTerminal k → ℝ}
    (hcov : tapeCovered (pgM k) δ x zt m) (t : ℕ) : qSel δ x zt t = qEag δ x zt t :=
  (ram_work_bounds_final (K := pgD k + 1) pgDag_wf (4 * 2 ^ k) pgDag_degree (pg_h0 k)
    (pg_nested hx hcov) (by omega) (pgRt k) cR cR_strictMono (1 / 5) (by norm_num)
    (fun _ => true) 0 0).1 t

/-! ### Work of the Graph-Selective monitor -/

/-- Computed cost of the Graph-Selective engine for the query at time `t` (stop scan,
leader scan, root-retirement scan, release cascade) and rollout `t + 1` (waves on the live
circuit, retirement tests and retirements, release cascade). -/
def selCost (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) : ℕ :=
  costF (pgD k + 1) (pgRt k) delivCand (pgUpd δ x zt) (fun _ => true)
    ⟨⟨pgDag k, (pgInit k).1, (pgInit k).2⟩, fun _ => true⟩ t

/-- **Total work of `T` rollouts under Graph Selective**: the shared charges of
`ParityGrid.pgWork` (initialisation, allocator work of every rollout), the computed engine
cost of the queries at times `0, …, T - 1` and of the rollouts `1, …, T`, and the final
leader-and-stop query at time `T` (two scans of the root actions). -/
def selWork (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (T : ℕ) : ℕ :=
  pgInitCost k + ∑ s ∈ range T, pgRolloutCost (sel s) (zt s)
    + ∑ t ∈ range T, selCost δ x zt t + pgQueryCost k

/-- Full-incidence deliveries of one rollout on the parity grid: at most `2 (4r + 2)`. -/
lemma pg_eagerPlus_le (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    eagerPlus (pgDag k) (pgUpd δ x zt) (pgInit k).1 (pgInit k).2 t ≤ 2 * (4 * 2 ^ k + 2) := by
  have h4 : (2 + 2 * 2 ^ k + 2 * 2 ^ k * 1) + (2 + 2 * 2 ^ k + 2 * 2 ^ k * 1)
      = 2 * (4 * 2 ^ k + 2) := by ring
  have hinv := pgState_inv δ x zt t
  obtain ⟨s0, s1, s2, s3⟩ := pgDag_shape (zt t)
  have v1 := vol_three_layers pgDag_wf (gid (vT (zt t))) (pgTab δ x zt (t + 1) (zt t)).1
    (pgState δ x zt t).1 (gid_lt _) hinv.1 2 (2 ^ k) 1 s0 s1 s2 s3
  have v2 := vol_three_layers pgDag_wf (gid (vT (zt t))) (pgTab δ x zt (t + 1) (zt t)).2
    (pgState δ x zt t).2 (gid_lt _) hinv.2 2 (2 ^ k) 1 s0 s1 s2 s3
  have hp : ((pgInit k).1, (pgInit k).2) = pgInit k := rfl
  unfold eagerPlus
  rw [hp]
  show vol (pgDag k) (pgState δ x zt t).1 (pgState δ x zt (t + 1)).1
    + vol (pgDag k) (pgState δ x zt t).2 (pgState δ x zt (t + 1)).2 ≤ _
  rw [pgState_succ, ivWave_fst]
  dsimp only
  exact (Nat.add_le_add v1 v2).trans (le_of_eq h4)

/-- **Engine work of the Graph-Selective monitor** (`eq:ram-work-bounds` with `D ≤ 4r`,
`L = 3`, `K = d + 1 ≤ 4r`, `S ≤ S₀ ≤ T (8r + 4)`, `R ≤ |E| ≤ 11 r²`). -/
theorem selCost_sum_le (hx : PGTape x) {m : GridTerminal k → ℝ}
    (hcov : tapeCovered (pgM k) δ x zt m) (T : ℕ) :
    ∑ t ∈ range T, selCost δ x zt t
      ≤ 36 * (2 ^ k * 2 ^ k) + (2 * k + 8) * (11 * (2 ^ k * 2 ^ k))
        + T * (16 * 2 ^ k + 12 + (k + 7) * (8 * 2 ^ k + 4)) := by
  obtain ⟨_, _, _, _, b5, b6, b7⟩ := ram_work_bounds_final (K := pgD k + 1) pgDag_wf
    (4 * 2 ^ k) pgDag_degree (pg_h0 k) (pg_nested hx hcov) (by omega) (pgRt k) cR
    cR_strictMono (1 / 5) (by norm_num) (fun _ => true) T 0
  have hQ : ((range T).filter (fun t => (fun _ : ℕ => true) t = true)).card = T := by simp
  have hcl : Nat.clog 2 (4 * 2 ^ k) ≤ k + 2 :=
    Nat.clog_le_of_le_pow (by rw [pow_succ, pow_succ]; omega)
  have hvol : ∑ t ∈ range T, volF (pgD k + 1) (pgRt k) delivCand (pgUpd δ x zt)
      (fun _ => true) ⟨⟨pgDag k, (pgInit k).1, (pgInit k).2⟩, fun _ => true⟩ t
      ≤ T * (8 * 2 ^ k + 4) := by
    refine b6.trans ?_
    have := Finset.sum_le_card_nsmul (range T)
      (fun t => eagerPlus (pgDag k) (pgUpd δ x zt) (pgInit k).1 (pgInit k).2 t)
      (2 * (4 * 2 ^ k + 2)) (fun t _ => pg_eagerPlus_le δ x zt t)
    rw [card_range, smul_eq_mul] at this
    refine this.trans (le_of_eq ?_)
    ring
  have hlive : live (pgDag k) = pgE k := rfl
  have hL : (pgDag k).L = 3 := rfl
  obtain ⟨-, hN, -, hE⟩ := pgDag_size (k := k)
  have hd := pgD_le (k := k)
  rw [hlive] at b5 b7
  rw [hQ, hL] at b5
  have A1 := Nat.mul_le_mul (show Nat.clog 2 (4 * 2 ^ k) + 5 ≤ k + 7 by omega) hvol
  have A2 := Nat.mul_le_mul (show 2 * Nat.clog 2 (4 * 2 ^ k) + 4 ≤ 2 * k + 8 by omega)
    (b7.trans hE)
  have A3 : T * (4 * (pgD k + 1)) ≤ T * (16 * 2 ^ k) := Nat.mul_le_mul_left _ (by omega)
  have e : T * (16 * 2 ^ k + 12 + (k + 7) * (8 * 2 ^ k + 4))
      = T * (16 * 2 ^ k) + 12 * T + (k + 7) * (T * (8 * 2 ^ k + 4)) := by ring
  rw [e]
  show ∑ t ∈ range T, costF (pgD k + 1) (pgRt k) delivCand (pgUpd δ x zt) (fun _ => true)
    ⟨⟨pgDag k, (pgInit k).1, (pgInit k).2⟩, fun _ => true⟩ t ≤ _
  omega

/-- **Total work under Graph Selective, in natural numbers.** -/
theorem selWork_le (hx : PGTape x) {m : GridTerminal k → ℝ}
    (hcov : tapeCovered (pgM k) δ x zt m) (sel : ℕ → Fin (pgD k + 1)) (T : ℕ) :
    selWork δ x sel zt T
      ≤ 72 * (2 ^ k * 2 ^ k) + 8 * 2 ^ k + (2 * k + 8) * (11 * (2 ^ k * 2 ^ k))
        + T * (23 * 2 ^ k + 18 + (k + 7) * (8 * 2 ^ k + 4)) := by
  have h0 := selCost_sum_le hx hcov T
  obtain ⟨-, hN, -, hE⟩ := pgDag_size (k := k)
  have hd := pgD_le (k := k)
  have h1 : ∑ s ∈ range T, pgRolloutCost (sel s) (zt s) ≤ T * (7 * 2 ^ k + 6) := by
    have := Finset.sum_le_card_nsmul (range T) (fun s => pgRolloutCost (sel s) (zt s))
      (7 * 2 ^ k + 6) (fun s _ => pgRolloutCost_le _ _)
    rwa [card_range, smul_eq_mul] at this
  have e : T * (23 * 2 ^ k + 18 + (k + 7) * (8 * 2 ^ k + 4))
      = T * (7 * 2 ^ k + 6) + T * (16 * 2 ^ k + 12 + (k + 7) * (8 * 2 ^ k + 4)) := by ring
  rw [e]
  unfold selWork pgInitCost pgQueryCost
  omega

end Monitors

/-! ## Assembly: `thm:coded-covers` with both monitors -/

section Final

variable {k : ℕ}

/-- The pathwise conclusion of the upper half of `thm:coded-covers` for BOTH monitors, for
a search `(sel, zt)` on the tapes `x`.  There is a rollout count `τ` such that

* (Graph Eager, as in `ParityGrid.PGCertified`) the root query first stops at `τ`, it
  recommends `w*` there, and any successful query recommends `w*`;
* (coupling) after every rollout the Graph-Selective query returns the same leader and the
  same stopping bit as the Graph-Eager query, and the eager query returns `(some a, true)`
  exactly when `pgStops … a`;
* (Graph Selective) its query returns `(some d, true)` at `τ` (`d` is the index of `w*`),
  its stop bit is `false` before `τ`, and whenever its stop bit is set its leader is `w*`;
* `τ ≤ A r log r`;
* the total work up to `τ` is at most `B r² log² r` for the eager monitor (`pgWork`) and
  for the selective monitor (`selWork`). -/
def PGCertifiedBoth (δ A B : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) : Prop :=
  ∃ τ : ℕ, pgStops δ x zt τ (Fin.last _) ∧
    (∀ t, t < τ → ∀ a, ¬ pgStops δ x zt t a) ∧
    (∀ t a, pgStops δ x zt t a → a = Fin.last _) ∧
    (∀ t, qSel δ x zt t = qEag δ x zt t) ∧
    (∀ t (a : Fin (pgD k + 1)), qEag δ x zt t = (some (a : ℕ), true) ↔ pgStops δ x zt t a) ∧
    qSel δ x zt τ = (some (pgD k), true) ∧
    (∀ t, t < τ → (qSel δ x zt t).2 = false) ∧
    (∀ t, (qSel δ x zt t).2 = true → (qSel δ x zt t).1 = some (pgD k)) ∧
    (τ : ℝ) ≤ A * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) ∧
    (pgWork δ x sel zt τ : ℝ) ≤ B * ((2 : ℝ) ^ k) ^ 2 * Real.log ((2 : ℝ) ^ k) ^ 2 ∧
    (selWork δ x sel zt τ : ℝ) ≤ B * ((2 : ℝ) ^ k) ^ 2 * Real.log ((2 : ℝ) ^ k) ^ 2

/-- **Step 3 of `thm:coded-covers`, pathwise, for both monitors.**  Fix `δ ∈ (0, 1)`.
There are constants `A, B` such that for every `k ≥ 2`, every reward tape with the stated
ranges, every UCT search on the parity-grid DAG, and every run on which the means lie in
the Hoeffding boxes at all times (the coverage event), the conclusion `PGCertifiedBoth`
holds.  The coverage hypothesis is used only for the Graph-Selective monitor (it makes the
terminal updates nested with nonempty intervals). -/
theorem parity_certified_both {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1)) (zt : ℕ → GridTerminal k),
      PGTape x → ParitySearch x sel zt → tapeCovered (pgM k) δ x zt (pgMean k) →
      PGCertifiedBoth δ A B x sel zt := by
  obtain ⟨A, B, hA, hB, hpath⟩ := parity_certified hδ0 hδ1
  refine ⟨A, B + 109 * A + 206, hA, by nlinarith, ?_⟩
  intro k hk x sel zt hx h hcov
  obtain ⟨τ, c1, c2, c3, c4, c5⟩ := hpath k hk x sel zt hx h
  have hcpl : ∀ t, qSel δ x zt t = qEag δ x zt t := fun t => qSel_eq_qEag hx hcov t
  have hiff : ∀ t (a : Fin (pgD k + 1)),
      qEag δ x zt t = (some (a : ℕ), true) ↔ pgStops δ x zt t a := fun t a => qEag_iff δ x zt t a
  have hbit : ∀ t, (qSel δ x zt t).2 = true →
      ∃ a : Fin (pgD k + 1), qSel δ x zt t = (some (a : ℕ), true) := fun t ht =>
    qOut_stop (pgD k + 1) _ _ (1 / 5) _ ht
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ) ^ k := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log r := ⟨_, rfl⟩
  have hr4 : (4 : ℝ) ≤ r := by
    rw [hr]
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hl2 := Real.log_two_gt_d9
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hℓk : ℓ = k * Real.log 2 := by rw [hℓ, hr, Real.log_pow]
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓk]
    nlinarith
  have hk2 : (k : ℝ) ≤ 2 * ℓ := by
    rw [hℓk]
    nlinarith
  rw [← hr, ← hℓ] at c4 c5
  have hr2 : 16 ≤ r ^ 2 := by nlinarith
  have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
  have hrl0 : (0 : ℝ) ≤ r ^ 2 * ℓ ^ 2 := by positivity
  refine ⟨τ, c1, c2, c3, hcpl, hiff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcpl τ]
    exact (hiff τ (Fin.last _)).2 c1
  · intro t ht
    by_contra hne
    have htrue : (qSel δ x zt t).2 = true := by simpa using hne
    obtain ⟨a, ha⟩ := hbit t htrue
    rw [hcpl t] at ha
    exact c2 t ht a ((hiff t a).1 ha)
  · intro t ht
    obtain ⟨a, ha⟩ := hbit t ht
    have ha' := ha
    rw [hcpl t] at ha'
    have hal := c3 t a ((hiff t a).1 ha')
    rw [ha, hal]
    rfl
  · rw [← hr, ← hℓ]
    exact c4
  · rw [← hr, ← hℓ]
    have e : (B + 109 * A + 206) * r ^ 2 * ℓ ^ 2
        = B * r ^ 2 * ℓ ^ 2 + (109 * A + 206) * (r ^ 2 * ℓ ^ 2) := by ring
    have h0 : 0 ≤ (109 * A + 206) * (r ^ 2 * ℓ ^ 2) := mul_nonneg (by linarith) hrl0
    linarith
  · rw [← hr, ← hℓ]
    have hW := selWork_le hx hcov sel τ
    have hWR : (selWork δ x sel zt τ : ℝ) ≤ 72 * (r * r) + 8 * r
        + (2 * (k : ℝ) + 8) * (11 * (r * r))
        + τ * (23 * r + 18 + ((k : ℝ) + 7) * (8 * r + 4)) := by
      rw [hr]
      exact_mod_cast hW
    have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
    have hk7 : (k : ℝ) + 7 ≤ 9 * ℓ := by linarith
    have h84 : 8 * r + 4 ≤ 9 * r := by linarith
    have hp : ((k : ℝ) + 7) * (8 * r + 4) ≤ 9 * ℓ * (9 * r) :=
      mul_le_mul hk7 h84 (by linarith) (by linarith)
    have hrℓ : r ≤ r * ℓ := le_mul_of_one_le_right (by linarith) hℓ1
    have hper : 23 * r + 18 + ((k : ℝ) + 7) * (8 * r + 4) ≤ 109 * (r * ℓ) := by
      nlinarith
    have hper0 : (0 : ℝ) ≤ 23 * r + 18 + ((k : ℝ) + 7) * (8 * r + 4) := by
      have : (0 : ℝ) ≤ ((k : ℝ) + 7) * (8 * r + 4) := by positivity
      linarith
    have h1 : (τ : ℝ) * (23 * r + 18 + ((k : ℝ) + 7) * (8 * r + 4))
        ≤ A * r * ℓ * (109 * (r * ℓ)) :=
      mul_le_mul c4 hper hper0 (by positivity)
    have hc : r ^ 2 ≤ r ^ 2 * ℓ ^ 2 := le_mul_of_one_le_right (by positivity) hℓ2
    have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
    have h2 : 72 * (r * r) + 8 * r ≤ 74 * (r ^ 2 * ℓ ^ 2) := by
      have hb : 8 * r ≤ 2 * r ^ 2 := by nlinarith
      nlinarith
    have h3 : (2 * (k : ℝ) + 8) * (11 * (r * r)) ≤ 132 * (r ^ 2 * ℓ ^ 2) := by
      have h31 : 2 * (k : ℝ) + 8 ≤ 12 * ℓ := by linarith
      have h32 : (2 * (k : ℝ) + 8) * (11 * (r * r)) ≤ 12 * ℓ * (11 * (r * r)) :=
        mul_le_mul_of_nonneg_right h31 (by positivity)
      have h33 : r ^ 2 * ℓ ≤ r ^ 2 * ℓ ^ 2 := mul_le_mul_of_nonneg_left hℓℓ (by positivity)
      nlinarith
    have hB0 : 0 ≤ B * (r ^ 2 * ℓ ^ 2) := mul_nonneg hB.le hrl0
    have e : (B + 109 * A + 206) * r ^ 2 * ℓ ^ 2
        = B * (r ^ 2 * ℓ ^ 2) + A * r * ℓ * (109 * (r * ℓ)) + 74 * (r ^ 2 * ℓ ^ 2)
          + 132 * (r ^ 2 * ℓ ^ 2) := by ring
    linarith

/-- **Theorem `thm:coded-covers` (and `thm:coded-main`) with both monitors.**  Fix
`δ ∈ (0, 1)`.  There are constants `A, B` (depending only on `δ`) such that for every
`k ≥ 2`, with `r = 2^k`:

1. `pgDag k` has `r² ≤ |V| ≤ 7r²` vertices and `2r² ≤ |E| ≤ 11r²` edges, its `d + 1`
   root supports are pairwise distinct, and `w*` is the unique `1/5`-optimal root action;
2. (every layout) every family of dyadic covers of the parity root supports under any
   terminal ordering has at least `r³ / 2` blocks in total;
3. for every probability space carrying reward tapes that are independent within each
   tape, have the stated ranges almost surely and the stated means, and for every UCT
   search (`c = 2`) run on these tapes: outside an event of probability at most `δ`, the
   true means lie in the Hoeffding box at every time and `PGCertifiedBoth` holds, i.e.
   Graph Eager and Graph Selective return the same leader and stopping bit after every
   rollout, both first stop at the same `τ ≤ A r log r`, both recommend `w*`, and the
   total work of each up to `τ` is at most `B r² log² r`.

The Graph-Selective monitor is `RetireFinal.runF` (strict-dominance retirement with the
delivery policy, release of orphaned gates, root-action retirement at the query after
every rollout).  The confidence alarm is not modelled: the statement is about the coverage
event only. -/
theorem coded_covers_selective {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ k : ℕ, 2 ≤ k →
      (2 ^ k * 2 ^ k ≤ (pgDag k).N ∧ (pgDag k).N ≤ 7 * (2 ^ k * 2 ^ k) ∧
        2 * (2 ^ k * 2 ^ k) ≤ pgE k ∧ pgE k ≤ 11 * (2 ^ k * 2 ^ k)) ∧
      Function.Injective (pgSupp k) ∧
      (∀ (a : Fin (pgD k + 1)) (hne : (pgSupp k a).Nonempty),
        regret (pgSupp k a) hne (pgMean k) ≤ 1 / 5 ↔ a = Fin.last _) ∧
      (∀ (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1)) (C : ParityIndex k → Finset (Finset ℕ)),
        (∀ p ∈ parityActions k, IsDyadicCover (C p) (layoutPos π (paritySupp p))) →
        2 ^ k * 2 ^ k * 2 ^ k ≤ 2 * ∑ p ∈ parityActions k, (C p).card) ∧
      (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : GridTerminal k → ℕ → Ω → ℝ),
        (∀ z, ProbabilityTheory.iIndepFun (X z) P) → (∀ z i, AEMeasurable (X z i) P) →
        (∀ i, ∀ᵐ ω ∂P, X none i ω ∈ Set.Icc (0.98 : ℝ) 1) →
        (∀ g i, ∀ᵐ ω ∂P, X (some g) i ω ∈ Set.Icc (0.01 : ℝ) 0.03) →
        (∀ z i, ∫ ω, X z i ω ∂P = pgMean k z) →
        ∀ (sel : Ω → ℕ → Fin (pgD k + 1)) (zt : Ω → ℕ → GridTerminal k),
        (∀ ω, ParitySearch (fun z i => X z i ω) (sel ω) (zt ω)) →
        P {ω | ¬ (tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k) ∧
            PGCertifiedBoth δ A B (fun z i => X z i ω) (sel ω) (zt ω))} ≤ ENNReal.ofReal δ) := by
  obtain ⟨A, B, hA, hB, hpath⟩ := parity_certified_both hδ0 hδ1
  refine ⟨A, B, hA, hB, ?_⟩
  intro k hk
  refine ⟨pgDag_size, pgSupp_injective, pg_unique_optimal, ?_, ?_⟩
  · intro π C hC
    exact parityGrid_cover_lower (by omega) π C hC
  · intro Ω _ P _ X hindep hmeas hwin hgrid hmean sel zt hsearch
    have hbdd : ∀ z i, ∀ᵐ ω ∂P, X z i ω ∈ Set.Icc (0 : ℝ) 1 := by
      intro z i
      rcases z with _ | g
      · filter_upwards [hwin i] with ω hω
        exact ⟨by have := hω.1; linarith, hω.2⟩
      · filter_upwards [hgrid g i] with ω hω
        exact ⟨by have := hω.1; linarith, by have := hω.2; linarith⟩
    have hcard : (Fintype.card (GridTerminal k) : ℝ) ≤ pgM k := by
      have hm : Fintype.card (Mask k) = 2 ^ k := by
        rw [← card_univ, card_univ_mask]
      have : Fintype.card (GridTerminal k) = 2 ^ k * 2 ^ k + 1 := by
        rw [Fintype.card_option, Fintype.card_prod, hm]
      unfold pgM
      rw [this]
    have hM1 : (1 : ℝ) ≤ pgM k := by
      have := pgM_ge (k := k)
      linarith
    have hcov := tape_coverage P hindep hmeas hbdd hmean hM1 hcard hδ0 hδ1.le zt
    have hae : ∀ᵐ ω ∂P, PGTape (fun z i => X z i ω) := by
      have h1 : ∀ᵐ ω ∂P, ∀ i, X none i ω ∈ Set.Icc (0.98 : ℝ) 1 := ae_all_iff.2 hwin
      have h2 : ∀ᵐ ω ∂P, ∀ g i, X (some g) i ω ∈ Set.Icc (0.01 : ℝ) 0.03 :=
        ae_all_iff.2 (fun g => ae_all_iff.2 (hgrid g))
      filter_upwards [h1, h2] with ω a b
      exact ⟨a, b⟩
    have hnull : P {ω | ¬ PGTape (fun z i => X z i ω)} = 0 := ae_iff.1 hae
    have hsub : {ω | ¬ (tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k) ∧
          PGCertifiedBoth δ A B (fun z i => X z i ω) (sel ω) (zt ω))}
        ⊆ {ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          ∪ {ω | ¬ PGTape (fun z i => X z i ω)} := by
      intro ω hω
      by_cases hx : PGTape (fun z i => X z i ω)
      · left
        intro hc
        exact hω ⟨hc, hpath k hk _ _ _ hx (hsearch ω) hc⟩
      · right
        exact hx
    calc P {ω | ¬ (tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k) ∧
            PGCertifiedBoth δ A B (fun z i => X z i ω) (sel ω) (zt ω))}
        ≤ P ({ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          ∪ {ω | ¬ PGTape (fun z i => X z i ω)}) := measure_mono hsub
      _ ≤ P {ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          + P {ω | ¬ PGTape (fun z i => X z i ω)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ := by
          rw [hnull, add_zero]
          exact hcov

end Final

end

end LiteralK2
end JointRootCert
