/-
Audit follow-ups for Theorem `thm:v2separation` (Root-PUCT work separation from uninformative
initialization), Corollary `cor:v2quarter` (One explicit polynomial instance) and Theorem
`thm:ta-core` (Wide Common-Core Support Compilation Cost).

1. Identical leaders.  `LiteralE5.box_outputs` proves that the selective and the full monitor
   return the same output (`MonOut`: leader set and stopping set) at every count along the
   continued trace, but `v2separation_literal` / `v2quarter_literal` only export the coupling of
   the controller states.  `v2separation_full` and `v2quarter_full` add: at every time `t` of
   the coupled closed loops the two monitors expose the same interface (`Iface`: failure flag
   and `MonOut`), in particular the same leaders.

2. Local UCT inside the hub.  `LiteralE7.ta_core_both_readings` allows an arbitrary path rule
   below the root.  `FullCoreSearch` is the search on the common-core DAG in which every
   internal vertex is a local UCT node (`eq:uct-index`, `c_uct = 2`, first visits try the
   untried edges, then any maximiser) on its own visit clock, with empirical means of the
   rewards of the terminals actually reached: the root, every losing-action vertex
   (`bin hub priv_i`) and every binary vertex of the shared hub.  The hub is one shared
   subgraph of the DAG, so its visit clock counts the rollouts entering it through any losing
   action (`hubN`).  The reading of `N_t(v)` is the parameter `lit` (`false`:
   `log (1 + N)`, `true`: `log N`), used at every vertex.  `exists_fullCoreSearch`,
   `fullCoreRule` (the induced path rule), `fullCoreRule_walk`, `FullCoreSearch.either`
   (reduction to `CoreSearch ∨ LitCoreSearch`, same root process), `ta_core_full`.
-/
import JointRootCert.LiteralE5
import JointRootCert.LiteralE7

namespace JointRootCert

namespace LiteralF5

open Finset

noncomputable section

/-! ## 1. Identical leaders in `thm:v2separation` and `cor:v2quarter` -/

section V2

open LiteralE5

/-- On every state of the continued trace the two monitors in the loop expose the same
interface: the same failure flag and the same output (leaders and stopping set). -/
theorem ctlMon_free_eq (m : ℕ) {g δ : ℝ} (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8) (hpick : IsPuctPick pick)
    (j : ℕ) (st : Status) :
    ctlMon true m δ (g / 2) ⟨freeH m g rule pick j, st⟩
      = ctlMon false m δ (g / 2) ⟨freeH m g rule pick j, st⟩ := by
  have htr := (free_graphRun m g rule pick hpick).trace
  have hlow : ∀ k, k ≤ 3 → ∀ a, freeN m g rule pick k a ≤ 1 :=
    fun k hk a => freeN_le_one m g rule pick hk a
  have ho : (ctlMon true m δ (g / 2) ⟨freeH m g rule pick j, st⟩).out
      = (ctlMon false m δ (g / 2) ⟨freeH m g rule pick j, st⟩).out := by
    rw [ctlMon_free_out, ctlMon_free_out]
    exact (box_outputs hδ0 hδ hg hg8 hlow htr m).1 j
  exact congrArg (Iface.mk (∃ z, (histTab δ (freeH m g rule pick j) z).2
    < (histTab δ (freeH m g rule pick j) z).1)) ho

/-- Along coupled closed loops the two monitors expose the same interface at every time. -/
theorem loops_agree (m : ℕ) {g δ : ℝ} (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3)
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hg : 0 < g) (hg8 : g ≤ 1 / 8) (hpick : IsPuctPick pick)
    (hc : ∀ t, closedLoop m g rule pick true δ t = closedLoop m g rule pick false δ t)
    (t : ℕ) :
    ctlMon true m δ (g / 2) (closedLoop m g rule pick true δ t)
      = ctlMon false m δ (g / 2) (closedLoop m g rule pick false δ t) := by
  obtain ⟨j, st, hj⟩ := closedLoop_reach m g rule pick true δ t
  rw [← hc t, hj]
  exact ctlMon_free_eq m rule pick hδ0 hδ hg hg8 hpick j st

/-- **Theorem `thm:v2separation`, with identical leaders.**  All conclusions of
`LiteralE5.v2separation_literal` (same constants), and in addition: at every time `t` the
selective and the full monitor, each in its own closed loop (the two loops are equal,
`SeparationBounds.run.coupled`), expose the same interface (failure flag and `MonOut`), in
particular the same leader set. -/
theorem v2separation_full {δ α : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (hα0 : 0 < α)
    (hα : α < 1 / 2) :
    ∃ (m0 T : ℕ) (cτ Cτ cH CH C1 cF CF : ℝ), 0 < cτ ∧ 0 < cH ∧ 0 < C1 ∧ 0 < cF ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-α) →
      ∀ (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3), IsPuctPick pick →
      ∃ tc τ : ℕ, tc ≤ T ∧
        SeparationBounds m δ g rule pick tc τ cτ Cτ cH CH C1 cF CF
          ((m : ℝ) ^ (2 * α) * Real.log m ^ 2) ((m : ℝ) ^ α * Real.log m)
          ((m : ℝ) ^ (1 + α) * Real.log m) ∧
        (∀ t, ctlMon true m δ (g / 2) (closedLoop m g rule pick true δ t)
          = ctlMon false m δ (g / 2) (closedLoop m g rule pick false δ t)) ∧
        (∀ t, (ctlMon true m δ (g / 2) (closedLoop m g rule pick true δ t)).out.leaders
          = (ctlMon false m δ (g / 2) (closedLoop m g rule pick false δ t)).out.leaders) := by
  obtain ⟨m0, T, cτ, Cτ, cH, CH, C1, cF, CF, p1, p2, p3, p4, H⟩ :=
    v2separation_literal hδ0 hδ hα0 hα
  obtain ⟨m1, _, _, _, _, _, _, _, _, _, _, _, _, H1⟩ := v2separation_firstcut hδ0 hδ hα0 hα
  refine ⟨max m0 m1, T, cτ, Cτ, cH, CH, C1, cF, CF, p1, p2, p3, p4, ?_⟩
  intro m hm g hg rule pick hpick
  obtain ⟨hgpos, hg8, -⟩ := H1 m (le_trans (le_max_right _ _) hm) g hg rule _ _ _
    (free_graphRun m g rule pick hpick)
  obtain ⟨tc, τ, htc, hB⟩ := H m (le_trans (le_max_left _ _) hm) g hg rule pick hpick
  have hagree := loops_agree m rule pick hδ0 hδ hgpos hg8 hpick hB.run.coupled
  exact ⟨tc, τ, htc, hB, hagree, fun t => congrArg (fun o : Iface => o.out.leaders) (hagree t)⟩

/-- **Corollary `cor:v2quarter`, with identical leaders.**  All conclusions of
`LiteralE5.v2quarter_literal` (same constants), and in addition the two monitors expose the
same interface, in particular the same leaders, at every time of the coupled closed loops. -/
theorem v2quarter_full {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) :
    ∃ (m0 T : ℕ) (cτ Cτ cH CH C1 cF CF cR CR : ℝ),
      0 < cτ ∧ 0 < cH ∧ 0 < C1 ∧ 0 < cF ∧ 0 < cR ∧
      ∀ m : ℕ, m0 ≤ m → ∀ g : ℝ, g = (m : ℝ) ^ (-(1 / 4 : ℝ)) →
      ∀ (rule : ℕ → ℕ → Bool) (pick : Hist → Fin 3), IsPuctPick pick →
      ∃ tc τ : ℕ, tc ≤ T ∧
        SeparationBounds m δ g rule pick tc τ cτ Cτ cH CH C1 cF CF
          ((m : ℝ) ^ (1 / 2 : ℝ) * Real.log m ^ 2) ((m : ℝ) ^ (1 / 4 : ℝ) * Real.log m)
          ((m : ℝ) ^ (5 / 4 : ℝ) * Real.log m) ∧
        cR * ((m : ℝ) ^ (1 / 4 : ℝ) * Real.log m)
          ≤ (histWork false m δ (g / 2) rule (freeH m g rule pick τ) : ℝ)
            / histWork true m δ (g / 2) rule (freeH m g rule pick τ) ∧
        (histWork false m δ (g / 2) rule (freeH m g rule pick τ) : ℝ)
            / histWork true m δ (g / 2) rule (freeH m g rule pick τ)
          ≤ CR * ((m : ℝ) ^ (1 / 4 : ℝ) * Real.log m) ∧
        (∀ t, ctlMon true m δ (g / 2) (closedLoop m g rule pick true δ t)
          = ctlMon false m δ (g / 2) (closedLoop m g rule pick false δ t)) ∧
        (∀ t, (ctlMon true m δ (g / 2) (closedLoop m g rule pick true δ t)).out.leaders
          = (ctlMon false m δ (g / 2) (closedLoop m g rule pick false δ t)).out.leaders) := by
  obtain ⟨m0, T, cτ, Cτ, cH, CH, C1, cF, CF, cR, CR, p1, p2, p3, p4, p5, H⟩ :=
    v2quarter_literal hδ0 hδ
  obtain ⟨m1, _, _, _, _, _, _, _, _, _, _, _, _, H1⟩ :=
    v2separation_firstcut hδ0 hδ (α := 1 / 4) (by norm_num) (by norm_num)
  refine ⟨max m0 m1, T, cτ, Cτ, cH, CH, C1, cF, CF, cR, CR, p1, p2, p3, p4, p5, ?_⟩
  intro m hm g hg rule pick hpick
  obtain ⟨hgpos, hg8, -⟩ := H1 m (le_trans (le_max_right _ _) hm) g hg rule _ _ _
    (free_graphRun m g rule pick hpick)
  obtain ⟨tc, τ, htc, hB, hr1, hr2⟩ := H m (le_trans (le_max_left _ _) hm) g hg rule pick hpick
  have hagree := loops_agree m rule pick hδ0 hδ hgpos hg8 hpick hB.run.coupled
  exact ⟨tc, τ, htc, hB, hr1, hr2, hagree,
    fun t => congrArg (fun o : Iface => o.out.leaders) (hagree t)⟩

end V2

/-! ## 2. `thm:ta-core` with local UCT at every vertex -/

section Node

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A local UCT node of `eq:uct-index` with `c_uct = 2`, under the reading `lit` of
`N_t(v)`: `lit = false` uses `log (1 + t)` (`UCTRun`), `lit = true` uses `log t`
(`LiteralE2.LitUCTRun`), `t` the number of earlier visits of the node.  The first `|ι|`
visits try every edge once, afterwards a maximiser of the index is taken. -/
def NodeRun (lit : Bool) (Q : ℕ → ι → ℝ) (sel : ℕ → ι) : Prop :=
  match lit with
  | true => LiteralE2.LitUCTRun 2 Q sel
  | false => UCTRun 2 Q sel

theorem exists_nodeRun [Nonempty ι] (lit : Bool) (Qf : (ℕ → ι) → ℕ → ι → ℝ)
    (hQ : ∀ (sel sel' : ℕ → ι) (t : ℕ), (∀ s, s < t → sel s = sel' s) → Qf sel t = Qf sel' t) :
    ∃ sel, NodeRun lit (Qf sel) sel := by
  cases lit
  · exact exists_uctRun 2 Qf hQ
  · exact LiteralE2.exists_litRun 2 Qf hQ

end Node

section Tree

variable {Z : Type*}

theorem fanLeaf_allTerm {P : Z → Prop} (arm : List Bool → ℕ → Fin 2) :
    ∀ c : MaxCirc Z, MaxCirc.AllTerm P c → ∀ v n, P (LiteralE2.fanLeaf arm c v n)
  | .term _, h, _, _ => h
  | .unary c, h, v, n => fanLeaf_allTerm arm c h (v ++ [true]) n
  | .bin c d, h, v, n => by
      have h' : MaxCirc.AllTerm P c ∧ MaxCirc.AllTerm P d := h
      simp only [LiteralE2.fanLeaf]
      split_ifs
      · exact fanLeaf_allTerm arm c h'.1 _ _
      · exact fanLeaf_allTerm arm d h'.2 _ _

/-- A path rule that follows the local decisions `fanDec` makes the sampler's walk
(`uctWalk`) reach the terminal `fanLeaf` of those decisions. -/
theorem fanDec_uctWalk (arm : List Bool → ℕ → Fin 2) (ρ : ℕ → Bool) :
    ∀ (c : MaxCirc Z) (v : List Bool) (n d0 : ℕ),
      (∀ k, ρ (d0 + k) = LiteralE2.fanDec arm c v n k) →
        (c.uctWalk ρ d0).1 = LiteralE2.fanLeaf arm c v n
  | .term _, _, _, _, _ => rfl
  | .unary c, v, n, d0, h => by
      have ih := fanDec_uctWalk arm ρ c (v ++ [true]) n (d0 + 1) (fun k => by
        have h1 := h (k + 1)
        simp only [LiteralE2.fanDec] at h1
        rw [show d0 + 1 + k = d0 + (k + 1) by omega]
        exact h1)
      simp only [MaxCirc.uctWalk, LiteralE2.fanLeaf]
      exact ih
  | .bin c e, v, n, d0, h => by
      have h0 : ρ d0 = decide (arm v n = 0) := by
        have h1 := h 0
        simp only [LiteralE2.fanDec, Nat.add_zero] at h1
        exact h1
      by_cases ha : arm v n = 0
      · have hr : ρ d0 = true := by rw [h0]; exact decide_eq_true ha
        have ih := fanDec_uctWalk arm ρ c (v ++ [true]) (uctCount (arm v) n 0) (d0 + 1)
          (fun k => by
            have h1 := h (k + 1)
            simp only [LiteralE2.fanDec, ite_eq_left ha] at h1
            rw [show d0 + 1 + k = d0 + (k + 1) by omega]
            exact h1)
        simp only [MaxCirc.uctWalk, hr, Bool.cond_true, LiteralE2.fanLeaf, ite_eq_left ha]
        exact ih
      · have hr : ρ d0 = false := by rw [h0]; exact decide_eq_false ha
        have ih := fanDec_uctWalk arm ρ e (v ++ [false]) (uctCount (arm v) n 1) (d0 + 1)
          (fun k => by
            have h1 := h (k + 1)
            simp only [LiteralE2.fanDec, ite_eq_right ha] at h1
            rw [show d0 + 1 + k = d0 + (k + 1) by omega]
            exact h1)
        simp only [MaxCirc.uctWalk, hr, Bool.cond_false, LiteralE2.fanLeaf, ite_eq_right ha]
        exact ih

/-- Every binary vertex of a tree is a local UCT node (`NodeRun lit`) on its own visit
clock; the empirical mean of an edge is the average of the rewards `rew` of the terminals
reached by the earlier visits of the vertex that took the edge.  Addresses and visit clocks
as in `LiteralE2.fanLeaf`. -/
def TreeUCT (lit : Bool) (rew : Z → ℝ) (arm : List Bool → ℕ → Fin 2) :
    MaxCirc Z → List Bool → Prop
  | .term _, _ => True
  | .unary c, v => TreeUCT lit rew arm c (v ++ [true])
  | .bin c d, v =>
      NodeRun lit (fun j b => (∑ i ∈ (range j).filter (fun i => arm v i = b),
          rew (LiteralE2.fanLeaf arm (.bin c d) v i)) / uctCount (arm v) j b) (arm v) ∧
        TreeUCT lit rew arm c (v ++ [true]) ∧ TreeUCT lit rew arm d (v ++ [false])

/-- On a tree all of whose terminals have reward `0`, arms that are UCT runs for the
constant mean `0` make every binary vertex a local UCT node. -/
theorem treeUCT_of_zero (lit : Bool) (rew : Z → ℝ) (arm : List Bool → ℕ → Fin 2)
    (harm : ∀ v, NodeRun lit (fun _ _ => (0 : ℝ)) (arm v)) :
    ∀ (c : MaxCirc Z) (v : List Bool), MaxCirc.AllTerm (fun z => rew z = 0) c →
      TreeUCT lit rew arm c v
  | .term _, _, _ => trivial
  | .unary c, v, h => treeUCT_of_zero lit rew arm harm c (v ++ [true]) h
  | .bin c d, v, h => by
      have h' : MaxCirc.AllTerm (fun z => rew z = 0) c ∧
          MaxCirc.AllTerm (fun z => rew z = 0) d := h
      refine ⟨?_, treeUCT_of_zero lit rew arm harm c _ h'.1,
        treeUCT_of_zero lit rew arm harm d _ h'.2⟩
      have hQ : (fun j b => (∑ i ∈ (range j).filter (fun i => arm v i = b),
          rew (LiteralE2.fanLeaf arm (.bin c d) v i)) / (uctCount (arm v) j b : ℝ))
          = fun _ _ => (0 : ℝ) := by
        funext j b
        rw [Finset.sum_eq_zero (fun i _ =>
          fanLeaf_allTerm (P := fun z => rew z = 0) arm (.bin c d) h v i), zero_div]
      rw [hQ]
      exact harm v

end Tree

section Core

variable (r : ℕ) [NeZero r]

/-- Whether rollout `s` enters the shared hub: the root chose a losing action `i`, and the
vertex of `i` took its first edge (the hub) at its current visit number. -/
def hubEnter (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2) (s : ℕ) : Bool :=
  if h : ((sel s : Fin (r + 1)) : ℕ) < r then
    decide (act ⟨sel s, h⟩ (uctCount sel s (sel s)) = 0)
  else false

/-- Visit clock of the shared hub: the number of earlier rollouts that entered it (through
any losing action). -/
def hubN (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2) (s : ℕ) : ℕ :=
  ((range s).filter (fun u => hubEnter r sel act u = true)).card

/-- Terminal reached by rollout `s` of the full search.  `sel` are the root's choices (root
clock = rollout index), `act i` those of the vertex of losing action `i` (clock: visits of
`i`; `0` = hub, `1` = private leaf), `arm v` those of the hub vertex with address `v` (clock:
visits of that vertex, the hub root's clock being `hubN`). -/
def fullCoreTerm (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2)
    (arm : List Bool → ℕ → Fin 2) (s : ℕ) : CoreZ r :=
  if h : ((sel s : Fin (r + 1)) : ℕ) < r then
    if act ⟨sel s, h⟩ (uctCount sel s (sel s)) = 0 then
      LiteralE2.fanLeaf arm (coreHub r) [] (hubN r sel act s)
    else corePriv r ⟨sel s, h⟩
  else coreWinZ r

open Classical in
/-- The rollout at which the root takes action `a` for the `j`-th time (`0` if there is
none). -/
def visitTime (sel : ℕ → Fin (r + 1)) (a : Fin (r + 1)) (j : ℕ) : ℕ :=
  if h : ∃ s, sel s = a ∧ uctCount sel s a = j then Nat.find h else 0

/-- Terminal reached by the `j`-th visit of the vertex of losing action `i`. -/
def actLeaf (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2) (arm : List Bool → ℕ → Fin 2)
    (i : Fin r) (j : ℕ) : CoreZ r :=
  if act i j = 0 then
    LiteralE2.fanLeaf arm (coreHub r) [] (hubN r sel act (visitTime r sel (Fin.castSucc i) j))
  else corePriv r i

/-- **TA-UCT on the common-core DAG with local UCT at every vertex.**  The root, the vertex
of every losing action and every binary vertex of the shared hub are local UCT nodes
(`NodeRun lit`, `eq:uct-index` with `c_uct = 2` and the reading `lit` of `N_t(v)`) on their
own visit clocks, with the empirical means of the rewards of the terminals reached through
each edge. -/
structure FullCoreSearch (lit : Bool) (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2)
    (arm : List Bool → ℕ → Fin 2) : Prop where
  root : NodeRun lit (fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a),
    coreReward r (fullCoreTerm r sel act arm s)) / uctCount sel t a) sel
  lose : ∀ i : Fin r, NodeRun lit (fun j b => (∑ j' ∈ (range j).filter (fun j' => act i j' = b),
    coreReward r (actLeaf r sel act arm i j')) / uctCount (act i) j b) (act i)
  hub : TreeUCT lit (coreReward r) arm (coreHub r) []

/-- The path rule induced by a full search: at rollout `s`, depth `0` is the decision of the
losing-action vertex (`true` = hub), depth `k + 1` the decision of the hub vertex `k` edges
below the hub root, each at its current visit number. -/
def fullCoreRule (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2)
    (arm : List Bool → ℕ → Fin 2) (s : ℕ) : ℕ → Bool
  | 0 => hubEnter r sel act s
  | k + 1 => LiteralE2.fanDec arm (coreHub r) [] (hubN r sel act s) k

variable {r}

omit [NeZero r] in
/-- `visitTime` inverts the visit clock of a root action. -/
theorem visitTime_eq {sel : ℕ → Fin (r + 1)} {a : Fin (r + 1)} {s : ℕ} (hs : sel s = a) :
    visitTime r sel a (uctCount sel s a) = s := by
  have hex : ∃ u, sel u = a ∧ uctCount sel u a = uctCount sel s a := ⟨s, hs, rfl⟩
  unfold visitTime
  rw [dite_eq_left hex]
  have hspec := Nat.find_spec hex
  have hle : Nat.find hex ≤ s := Nat.find_min' hex ⟨hs, rfl⟩
  rcases Nat.lt_or_ge (Nat.find hex) s with hlt | hge
  · exfalso
    have h1 := uctCount_succ sel (Nat.find hex) a
    rw [ite_eq_left hspec.1] at h1
    have h2 := uctCount_mono sel a (show Nat.find hex + 1 ≤ s by omega)
    have h3 := hspec.2
    omega
  · omega

/-- The means of a losing-action vertex are those of the terminals actually reached: the
terminal of its visit at rollout `s` is the terminal of rollout `s`. -/
theorem actLeaf_eq {sel : ℕ → Fin (r + 1)} {act : Fin r → ℕ → Fin 2}
    {arm : List Bool → ℕ → Fin 2} {i : Fin r} {s : ℕ} (hs : sel s = Fin.castSucc i) :
    actLeaf r sel act arm i (uctCount sel s (Fin.castSucc i)) = fullCoreTerm r sel act arm s := by
  have hlt : ((sel s : Fin (r + 1)) : ℕ) < r := by rw [hs]; simp
  have hi : (⟨sel s, hlt⟩ : Fin r) = i := Fin.ext (by simp [hs])
  unfold actLeaf fullCoreTerm
  rw [visitTime_eq hs, dite_eq_left hlt, hi, hs]

/-- The walk of the sampler under the induced rule reaches the terminal of the rollout. -/
theorem fullCoreRule_walk (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2)
    (arm : List Bool → ℕ → Fin 2) (s : ℕ) :
    fullCoreTerm r sel act arm s
      = ((coreAct r (sel s)).uctWalk (fullCoreRule r sel act arm s) 0).1 := by
  by_cases h : ((sel s : Fin (r + 1)) : ℕ) < r
  · have hact : coreAct r (sel s) = .bin (coreHub r) (.term (corePriv r ⟨sel s, h⟩)) := by
      unfold coreAct
      rw [dite_eq_left h]
    rw [hact]
    by_cases ha : act ⟨sel s, h⟩ (uctCount sel s (sel s)) = 0
    · have h0 : fullCoreRule r sel act arm s 0 = true := by
        show hubEnter r sel act s = true
        unfold hubEnter
        rw [dite_eq_left h]
        exact decide_eq_true ha
      simp only [MaxCirc.uctWalk, h0, Bool.cond_true, zero_add]
      unfold fullCoreTerm
      rw [dite_eq_left h, ite_eq_left ha]
      exact (fanDec_uctWalk arm _ (coreHub r) [] _ 1 (fun k => by
        rw [show 1 + k = k + 1 by omega]
        rfl)).symm
    · have h0 : fullCoreRule r sel act arm s 0 = false := by
        show hubEnter r sel act s = false
        unfold hubEnter
        rw [dite_eq_left h]
        exact decide_eq_false ha
      simp only [MaxCirc.uctWalk, h0, Bool.cond_false]
      unfold fullCoreTerm
      rw [dite_eq_left h, ite_eq_right ha]
  · have hact : coreAct r (sel s) = .term (coreWinZ r) := by
      unfold coreAct
      rw [dite_eq_right h]
    rw [hact]
    unfold fullCoreTerm
    rw [dite_eq_right h]
    rfl

theorem actLeaf_reward (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2)
    (arm : List Bool → ℕ → Fin 2) (i : Fin r) (j : ℕ) :
    coreReward r (actLeaf r sel act arm i j) = 0 := by
  unfold actLeaf
  split_ifs
  · exact fanLeaf_allTerm (P := fun z => coreReward r z = 0) arm _ (coreHub_zero r) _ _
  · rfl

/-- **Reduction.**  A full search is a search of the type accepted by
`LiteralE7.ta_core_both_readings`, with the same root process `sel`, the induced path rule
`fullCoreRule` and the terminals `fullCoreTerm`: a `CoreSearch` under the reading
`log (1 + N)` and a `LitCoreSearch` under the reading `log N`. -/
theorem FullCoreSearch.reading {lit : Bool} {sel : ℕ → Fin (r + 1)} {act : Fin r → ℕ → Fin 2}
    {arm : List Bool → ℕ → Fin 2} (h : FullCoreSearch r lit sel act arm) :
    (lit = false → CoreSearch r (fullCoreRule r sel act arm) sel (fullCoreTerm r sel act arm)) ∧
      (lit = true →
        LiteralE7.LitCoreSearch r (fullCoreRule r sel act arm) sel (fullCoreTerm r sel act arm)) := by
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · subst hl
    exact ⟨fullCoreRule_walk sel act arm, h.root⟩
  · subst hl
    exact ⟨fullCoreRule_walk sel act arm, h.root⟩

theorem FullCoreSearch.either {lit : Bool} {sel : ℕ → Fin (r + 1)} {act : Fin r → ℕ → Fin 2}
    {arm : List Bool → ℕ → Fin 2} (h : FullCoreSearch r lit sel act arm) :
    CoreSearch r (fullCoreRule r sel act arm) sel (fullCoreTerm r sel act arm) ∨
      LiteralE7.LitCoreSearch r (fullCoreRule r sel act arm) sel (fullCoreTerm r sel act arm) := by
  cases lit
  · exact Or.inl (h.reading.1 rfl)
  · exact Or.inr (h.reading.2 rfl)

/-- Full searches exist for every `r` and both readings. -/
theorem exists_fullCoreSearch (r : ℕ) [NeZero r] (lit : Bool) :
    ∃ sel act arm, FullCoreSearch r lit sel act arm := by
  obtain ⟨z2, hz2⟩ := exists_nodeRun (ι := Fin 2) lit (fun _ _ _ => (0 : ℝ))
    (fun _ _ _ _ => rfl)
  let act : Fin r → ℕ → Fin 2 := fun _ => z2
  let arm : List Bool → ℕ → Fin 2 := fun _ => z2
  obtain ⟨sel, hsel⟩ := exists_nodeRun (ι := Fin (r + 1)) lit
    (fun sel t a => (∑ s ∈ (range t).filter (fun s => sel s = a), coreMu r (sel s))
      / uctCount sel t a)
    (fun sel sel' t hss => LiteralE2.mean_local (fun sel s => coreMu r (sel s))
      (fun sel sel' s h => by rw [h s le_rfl]) sel sel' t hss)
  refine ⟨sel, act, arm, ?_, ?_, ?_⟩
  · have hQ : (fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a),
        coreReward r (fullCoreTerm r sel act arm s)) / (uctCount sel t a : ℝ))
        = fun t a => (∑ s ∈ (range t).filter (fun s => sel s = a), coreMu r (sel s))
          / (uctCount sel t a : ℝ) := by
      funext t a
      congr 1
      exact Finset.sum_congr rfl (fun s _ =>
        LiteralE7.reward_of_reach (fullCoreRule_walk sel act arm) s)
    rw [hQ]
    exact hsel
  · intro i
    have hQ : (fun j b => (∑ j' ∈ (range j).filter (fun j' => act i j' = b),
        coreReward r (actLeaf r sel act arm i j')) / (uctCount (act i) j b : ℝ))
        = fun _ _ => (0 : ℝ) := by
      funext j b
      rw [Finset.sum_eq_zero (fun j' _ => actLeaf_reward sel act arm i j'), zero_div]
    rw [hQ]
    exact hz2
  · exact treeUCT_of_zero lit (coreReward r) arm (fun _ => hz2) (coreHub r) [] (coreHub_zero r)

open LiteralE in
/-- **Theorem `thm:ta-core` for TA-UCT with local UCT at every vertex.**  Every clause of
`LiteralE7.ta_core_both_readings` (same constants), for every full search
(`FullCoreSearch`: root, losing-action vertices and hub vertices all local UCT nodes of
`eq:uct-index` on their own visit clocks), under both readings of `N_t(v)` (`lit`), with the
sampler following the induced path rule `rule = fullCoreRule` and reaching the terminals
`zt = fullCoreTerm`. -/
theorem ta_core_full {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∀ (r : ℕ) [NeZero r], 2 ≤ r →
      ∀ (lit : Bool) (sel : ℕ → Fin (r + 1)) (act : Fin r → ℕ → Fin 2)
        (arm : List Bool → ℕ → Fin 2), FullCoreSearch r lit sel act arm →
      ∀ (rule : ℕ → ℕ → Bool) (zt : ℕ → CoreZ r),
        rule = fullCoreRule r sel act arm → zt = fullCoreTerm r sel act arm →
        (∀ k a,
          cvLo (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a
              = coreL r (coreBox r (coreRadius r δ) zt) k a ∧
            cvHi (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a
              = coreU r (coreBox r (coreRadius r δ) zt) k a) ∧
        (∀ (s : Bool) k a,
          cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a ↔
            coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
        ∃ τ : ℕ,
          cvStops (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) τ)
            (Fin.last r) ∧
          (∀ s : Bool, coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) τ)
            (coreBox r (coreRadius r δ) zt τ) (Fin.last r)) ∧
          (∀ k, k < τ → ∀ a, ¬ cvStops
            (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a) ∧
          (∀ (s : Bool) k, k < τ → ∀ a,
            ¬ coreStops (coreRun s (coreHub r) (coreBox r (coreRadius r δ) zt) k)
              (coreBox r (coreRadius r δ) zt k) a) ∧
          (∀ k a, cvStops
            (cvRun r (coreBox r (coreRadius r δ) zt) (fun k => zt (r + 1 + k)) k) a →
              a = Fin.last r) ∧
          ((r + 1 + τ : ℕ) : ℝ) ≤ A * r * Real.log r ∧
          (∀ s : Bool, (coreTotalWork s r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ B * (r : ℝ) ^ 2 * Real.log r) ∧
          (cvTotalWork r (coreRadius r δ) rule sel zt τ : ℝ)
            ≤ C * (r : ℝ) ^ 2 * Real.log r ^ 2 ∧
          r ^ 3 ≤ (flatAll (coreAct r) (List.finRange (r + 1))).2 ∧
          ∀ out : Fin (r + 1) → List (CoreZ r), (∀ a, coreSupp r a ⊆ (out a).toFinset) →
            r ^ 3 ≤ ∑ a : Fin (r + 1), (out a).length := by
  obtain ⟨A, B, C, hA, hB, hC, H⟩ := LiteralE7.ta_core_both_readings hδ0 hδ1
  refine ⟨A, B, C, hA, hB, hC, ?_⟩
  intro r _ hr lit sel act arm h rule zt hrule hzt
  subst hrule hzt
  exact H r hr _ sel _ h.either

end Core

end

end LiteralF5

end JointRootCert
