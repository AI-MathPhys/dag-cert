/-
Joint Root Certification: the parity-grid family as an actual search process.

Manuscript: Part III, subsection `app:representation`.  Results covered:

* `thm:coded-main` (Every-layout limit of flat dyadic compilation) and
* `thm:coded-covers` (Every-Layout Dyadic Cover Lower Bound), Steps 1 and 3 of the proof:
  the parity-grid DAG as a `CostEngines.Dag` (`pgDag`), its size, supports and shape; a
  UCT search on it with rewards read from tapes (`ParitySearch`); the stopping time and
  total work of the costed interval engine of `CostEngines.lean` on it; and the assembled
  statement `coded_main`, which combines these with the every-layout lower bound
  `Representation.parityGrid_cover_lower` (Step 2).

Model.

* Graph: vertices are the `r² + 1` terminals, the `2r` coordinate gates, the
  `d = 4(r - 1)` parity actions and the root (`PV`), numbered by a fixed bijection with
  `Fin N`.
* Search: `sel s` is the root action of rollout `s` and `zt s` the terminal reached, any
  terminal of the support of `sel s` (the selections below the root are unconstrained).  The
  root is a UCT node with `c = 2` and index `Q + 2 √(log (1 + t) / N)`; `Q` is the average
  of the observed rewards; the reward of rollout `s` is the next unread entry of the tape of
  `zt s`.
* Monitor: the eager interval engine of `CostEngines.lean` (one wave per endpoint after
  every rollout), with Hoeffding boxes `[tapeLo, tapeHi]` for `M = r² + 1` terminals, and a
  root query (`MarginalStops` at `ε = 1/5`) after every rollout.
* Work: the engine's computed wave costs; charged by definition: `2 (N + E)` for writing
  the initial values and heap keys of both endpoints, one unit per child of each node on the
  selected path plus `9` per rollout for the allocator and the terminal table, and
  `2 (d + 1)` per root query.

Not modelled: retirement (the "Graph Selective" monitor), the confidence alarm, and
recursive UCT below the root (left arbitrary).
-/
import JointRootCert.CostEngines
import JointRootCert.UCTWork
import JointRootCert.Assembly

namespace JointRootCert
namespace ParityGrid

open Finset MeasureTheory CostEngines _root_.JointRootCert.Representation

noncomputable section

/-! ## Step 1: the parity-grid DAG -/

section Graph

variable (k : ℕ)

/-- Number `d = 4 (r - 1)` of parity root actions, `r = 2^k`. -/
def pgD : ℕ := 4 * (2 ^ k - 1)

/-- A numbering of the parity actions. -/
def pgActEquiv : {p : ParityIndex k // p ∈ parityActions k} ≃ Fin (pgD k) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, card_parityActions, pgD])

/-- The parity index `(orientation, mask, bit)` of the `a`-th parity action. -/
def pgIdx (a : Fin (pgD k)) : ParityIndex k := ((pgActEquiv k).symm a).1

lemma pgIdx_mem (a : Fin (pgD k)) : pgIdx k a ∈ parityActions k := ((pgActEquiv k).symm a).2

lemma pgIdx_injective : Function.Injective (pgIdx k) := fun _ _ h =>
  (pgActEquiv k).symm.injective (Subtype.ext h)

lemma pgIdx_surj {p : ParityIndex k} (hp : p ∈ parityActions k) : ∃ a, pgIdx k a = p :=
  ⟨pgActEquiv k ⟨p, hp⟩, by simp [pgIdx]⟩

/-- Vertices of the parity-grid DAG: terminals (`none` is `w*`), coordinate gates
(`(true, i)` is the row gate `R_i`, `(false, j)` the column gate `C_j`), parity actions,
and the root. -/
abbrev PV := GridTerminal k ⊕ (Bool × Mask k) ⊕ Fin (pgD k) ⊕ Unit

variable {k}

/-- Terminal vertex. -/
abbrev vT (z : GridTerminal k) : PV k := Sum.inl z
/-- Coordinate gate. -/
abbrev vC (c : Bool × Mask k) : PV k := Sum.inr (Sum.inl c)
/-- Parity action gate. -/
abbrev vA (a : Fin (pgD k)) : PV k := Sum.inr (Sum.inr (Sum.inl a))
/-- Root. -/
abbrev vR : PV k := Sum.inr (Sum.inr (Sum.inr ()))

variable (k)

/-- `PEdge p c`: `c` is a child of `p`.  Row gate `R_i` has children `(i, j)`, column gate
`C_j` has children `(i, j)`; the parity action `(f, a, b)` has as children the coordinate
gates of orientation `f` with `⟨a, i⟩ = b`; the root has as children all parity actions and
the terminal `w*`. -/
def PEdge (p c : PV k) : Prop :=
  (∃ cc x, p = vC cc ∧ c = vT (some x) ∧ (if cc.1 then x.1 else x.2) = cc.2) ∨
  (∃ a cc, p = vA a ∧ c = vC cc ∧ (pgIdx k a).1 = cc.1 ∧
    (pgIdx k a).2.1 ⬝ᵥ cc.2 = (pgIdx k a).2.2) ∨
  (∃ a, p = vR ∧ c = vA a) ∨ (p = vR ∧ c = vT none)

/-- Layer of a vertex: terminals 0, coordinate gates 1, parity actions 2, root 3. -/
def rk : PV k → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr _)) => 3

variable {k}

lemma rk_le (v : PV k) : rk k v ≤ 3 := by
  rcases v with z | c | a | u <;> simp [rk]

lemma PEdge.rk_lt {p c : PV k} (h : PEdge k p c) : rk k c < rk k p := by
  rcases h with ⟨cc, x, rfl, rfl, -⟩ | ⟨a, cc, rfl, rfl, -⟩ | ⟨a, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp [rk]

lemma PEdge.of_child_term {p : PV k} {z : GridTerminal k} (h : PEdge k p (vT z)) :
    (∃ cc x, p = vC cc ∧ z = some x ∧ (if cc.1 then x.1 else x.2) = cc.2) ∨
      (p = vR ∧ z = none) := by
  rcases h with ⟨cc, x, rfl, h2, h3⟩ | ⟨a, cc, rfl, h2, -⟩ | ⟨a, rfl, h2⟩ | ⟨rfl, h2⟩
  · exact Or.inl ⟨cc, x, rfl, Sum.inl_injective h2, h3⟩
  · simp at h2
  · simp at h2
  · exact Or.inr ⟨rfl, Sum.inl_injective h2⟩

lemma PEdge.of_child_coord {p : PV k} {c : Bool × Mask k} (h : PEdge k p (vC c)) :
    ∃ a, p = vA a ∧ (pgIdx k a).1 = c.1 ∧ (pgIdx k a).2.1 ⬝ᵥ c.2 = (pgIdx k a).2.2 := by
  rcases h with ⟨cc, x, rfl, h2, -⟩ | ⟨a, cc, rfl, h2, h3⟩ | ⟨a, rfl, h2⟩ | ⟨rfl, h2⟩
  · simp at h2
  · have e : c = cc := Sum.inl_injective (Sum.inr_injective h2)
    subst e
    exact ⟨a, rfl, h3⟩
  · simp at h2
  · simp at h2

lemma PEdge.of_child_act {p : PV k} {a : Fin (pgD k)} (h : PEdge k p (vA a)) : p = vR := by
  rcases h with ⟨cc, x, rfl, h2, -⟩ | ⟨a, cc, rfl, h2, -⟩ | ⟨a, rfl, -⟩ | ⟨rfl, -⟩
  · simp at h2
  · simp at h2
  · rfl
  · rfl

lemma PEdge.not_child_root {p : PV k} (h : PEdge k p vR) : False := by
  rcases h with ⟨cc, x, rfl, h2, -⟩ | ⟨a, cc, rfl, h2, -⟩ | ⟨a, rfl, h2⟩ | ⟨rfl, h2⟩ <;>
    simp at h2

lemma PEdge.not_parent_term {z : GridTerminal k} {c : PV k} (h : PEdge k (vT z) c) : False := by
  rcases h with ⟨cc, x, h1, -⟩ | ⟨a, cc, h1, -⟩ | ⟨a, h1, -⟩ | ⟨h1, -⟩ <;> simp at h1

lemma PEdge.of_parent_coord {cc : Bool × Mask k} {c : PV k} (h : PEdge k (vC cc) c) :
    ∃ x, c = vT (some x) ∧ (if cc.1 then x.1 else x.2) = cc.2 := by
  rcases h with ⟨cc', x, h1, rfl, h3⟩ | ⟨a, cc', h1, -⟩ | ⟨a, h1, -⟩ | ⟨h1, -⟩
  · have e : cc = cc' := Sum.inl_injective (Sum.inr_injective h1)
    subst e
    exact ⟨x, rfl, h3⟩
  · simp at h1
  · simp at h1
  · simp at h1

lemma PEdge.of_parent_act {a : Fin (pgD k)} {c : PV k} (h : PEdge k (vA a) c) :
    ∃ cc, c = vC cc ∧ (pgIdx k a).1 = cc.1 ∧ (pgIdx k a).2.1 ⬝ᵥ cc.2 = (pgIdx k a).2.2 := by
  rcases h with ⟨cc', x, h1, -⟩ | ⟨a', cc', h1, rfl, h3⟩ | ⟨a', h1, -⟩ | ⟨h1, -⟩
  · simp at h1
  · have e : a = a' := Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h1))
    subst e
    exact ⟨cc', rfl, h3⟩
  · simp at h1
  · simp at h1

lemma PEdge.of_parent_root {c : PV k} (h : PEdge k vR c) : (∃ a, c = vA a) ∨ c = vT none := by
  rcases h with ⟨cc', x, h1, -⟩ | ⟨a', cc', h1, -⟩ | ⟨a', -, rfl⟩ | ⟨-, rfl⟩
  · simp at h1
  · simp at h1
  · exact Or.inl ⟨a', rfl⟩
  · exact Or.inr rfl

lemma pEdge_coord_term (cc : Bool × Mask k) (x : Mask k × Mask k)
    (h : (if cc.1 then x.1 else x.2) = cc.2) : PEdge k (vC cc) (vT (some x)) :=
  Or.inl ⟨cc, x, rfl, rfl, h⟩

lemma pEdge_act_coord (a : Fin (pgD k)) (cc : Bool × Mask k) (h1 : (pgIdx k a).1 = cc.1)
    (h2 : (pgIdx k a).2.1 ⬝ᵥ cc.2 = (pgIdx k a).2.2) : PEdge k (vA a) (vC cc) :=
  Or.inr (Or.inl ⟨a, cc, rfl, rfl, h1, h2⟩)

lemma pEdge_root_act (a : Fin (pgD k)) : PEdge k vR (vA a) := Or.inr (Or.inr (Or.inl ⟨a, rfl, rfl⟩))

lemma pEdge_root_win : PEdge k vR (vT none) := Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

variable (k)

open Classical in
/-- Children of a vertex. -/
def cV (p : PV k) : Finset (PV k) := univ.filter (fun c => PEdge k p c)

open Classical in
/-- Parents of a vertex. -/
def pV (c : PV k) : Finset (PV k) := univ.filter (fun p => PEdge k p c)

variable {k}

lemma mem_cV {p c : PV k} : c ∈ cV k p ↔ PEdge k p c := by simp [cV]

lemma mem_pV {p c : PV k} : p ∈ pV k c ↔ PEdge k p c := by simp [pV]

/-! ### Degrees -/

lemma card_univ_mask : (univ : Finset (Mask k)).card = 2 ^ k := card_mask k

lemma one_le_r : 1 ≤ 2 ^ k := Nat.one_le_two_pow

lemma pgD_le : pgD k + 4 = 4 * 2 ^ k := by
  have := one_le_r (k := k)
  unfold pgD
  omega

lemma cV_term (z : GridTerminal k) : cV k (vT z) = ∅ := by
  ext c
  simp only [mem_cV, notMem_empty, iff_false]
  exact fun h => h.not_parent_term

lemma cV_coord_card (cc : Bool × Mask k) : (cV k (vC cc)).card = 2 ^ k := by
  have himg : cV k (vC cc)
      = univ.image (fun j : Mask k => vT (some (if cc.1 then (cc.2, j) else (j, cc.2)))) := by
    ext c
    rw [mem_cV, mem_image]
    obtain ⟨f, i⟩ := cc
    constructor
    · intro h
      obtain ⟨x, rfl, hx⟩ := h.of_parent_coord
      obtain ⟨x1, x2⟩ := x
      cases f
      · exact ⟨x1, mem_univ _, by simp at hx; simp [hx]⟩
      · exact ⟨x2, mem_univ _, by simp at hx; simp [hx]⟩
    · rintro ⟨j, -, rfl⟩
      apply pEdge_coord_term
      cases f <;> simp
  rw [himg, card_image_of_injective, card_univ_mask]
  intro j j' h
  have h' := Option.some_injective _ (Sum.inl_injective h)
  obtain ⟨f, i⟩ := cc
  cases f
  · simpa using congrArg Prod.fst h'
  · simpa using congrArg Prod.snd h'

lemma cV_act_card_le (a : Fin (pgD k)) : (cV k (vA a)).card ≤ 2 * 2 ^ k := by
  have hsub : cV k (vA a) ⊆ univ.image (fun cc : Bool × Mask k => vC cc) := by
    intro c hc
    obtain ⟨cc, rfl, -⟩ := (mem_cV.1 hc).of_parent_act
    exact mem_image.2 ⟨cc, mem_univ _, rfl⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  rw [card_univ, Fintype.card_prod, Fintype.card_bool, ← card_univ, card_univ_mask]

lemma cV_root_card_le : (cV k (vR : PV k)).card ≤ pgD k + 1 := by
  classical
  have hsub : cV k (vR : PV k) ⊆ insert (vT none) (univ.image (fun a : Fin (pgD k) => vA a)) := by
    intro c hc
    rcases (mem_cV.1 hc).of_parent_root with ⟨a, rfl⟩ | rfl
    · exact mem_insert_of_mem (mem_image.2 ⟨a, mem_univ _, rfl⟩)
    · exact mem_insert_self _ _
  refine (card_le_card hsub).trans ((card_insert_le _ _).trans ?_)
  have := card_image_le (s := (univ : Finset (Fin (pgD k)))) (f := fun a : Fin (pgD k) => (vA a : PV k))
  rw [card_univ, Fintype.card_fin] at this
  omega

lemma cV_card_le (v : PV k) : (cV k v).card ≤ 4 * 2 ^ k := by
  have hr := one_le_r (k := k)
  have hd := pgD_le (k := k)
  rcases v with z | cc | a | u
  · show (cV k (vT z)).card ≤ _
    rw [cV_term]
    simp
  · show (cV k (vC cc)).card ≤ _
    rw [cV_coord_card]
    omega
  · show (cV k (vA a)).card ≤ _
    have := cV_act_card_le a
    omega
  · show (cV k (vR : PV k)).card ≤ _
    have := cV_root_card_le (k := k)
    omega

lemma pV_term_card_le (z : GridTerminal k) : (pV k (vT z)).card ≤ 2 := by
  classical
  rcases z with _ | x
  · have hsub : pV k (vT (none : GridTerminal k)) ⊆ {vR} := by
      intro p hp
      rcases (mem_pV.1 hp).of_child_term with ⟨cc, x, -, h, -⟩ | ⟨rfl, -⟩
      · simp at h
      · exact mem_singleton_self _
    exact (card_le_card hsub).trans (by simp)
  · have hsub : pV k (vT (some x)) ⊆ {vC (true, x.1), vC (false, x.2)} := by
      intro p hp
      rcases (mem_pV.1 hp).of_child_term with ⟨cc, y, rfl, h, hy⟩ | ⟨-, h⟩
      · have e : x = y := Option.some_injective _ h
        subst e
        obtain ⟨f, i⟩ := cc
        cases f
        · simp at hy
          simp [hy]
        · simp at hy
          simp [hy]
      · simp at h
    exact (card_le_card hsub).trans card_le_two

lemma pV_coord_card_le (cc : Bool × Mask k) : (pV k (vC cc)).card ≤ 2 ^ k := by
  rw [← card_univ_mask (k := k)]
  apply card_le_card_of_injOn
    (fun p : PV k => Sum.elim (fun _ => (0 : Mask k))
      (Sum.elim (fun _ => 0) (Sum.elim (fun a => (pgIdx k a).2.1) (fun _ => 0))) p)
  · intro p _
    simp
  · intro p hp p' hp' h
    obtain ⟨a, rfl, h1, h2⟩ := (mem_pV.1 (mem_coe.1 hp)).of_child_coord
    obtain ⟨a', rfl, h1', h2'⟩ := (mem_pV.1 (mem_coe.1 hp')).of_child_coord
    have hm : (pgIdx k a).2.1 = (pgIdx k a').2.1 := h
    have : pgIdx k a = pgIdx k a' := by
      refine Prod.ext (h1.trans h1'.symm) (Prod.ext hm ?_)
      rw [← h2, ← h2', hm]
    rw [pgIdx_injective k this]

lemma pV_act_card_le (a : Fin (pgD k)) : (pV k (vA a)).card ≤ 1 := by
  have hsub : pV k (vA a) ⊆ {vR} := by
    intro p hp
    rw [(mem_pV.1 hp).of_child_act]
    exact mem_singleton_self _
  exact (card_le_card hsub).trans (by simp)

lemma pV_root : pV k (vR : PV k) = ∅ := by
  ext p
  simp only [mem_pV, notMem_empty, iff_false]
  exact fun h => h.not_child_root

lemma pV_card_rk0 (v : PV k) : (pV k v).card ≤ 2 ^ k + 1 := by
  have hr := one_le_r (k := k)
  rcases v with z | cc | a | u
  · have := pV_term_card_le z
    show (pV k (vT z)).card ≤ _
    omega
  · have := pV_coord_card_le cc
    show (pV k (vC cc)).card ≤ _
    omega
  · have := pV_act_card_le a
    show (pV k (vA a)).card ≤ _
    omega
  · show (pV k (vR : PV k)).card ≤ _
    rw [pV_root]
    simp

lemma pV_card_rk1 {v : PV k} (h : 1 ≤ rk k v) : (pV k v).card ≤ 2 ^ k := by
  have hr := one_le_r (k := k)
  rcases v with z | cc | a | u
  · simp [rk] at h
  · exact pV_coord_card_le cc
  · have := pV_act_card_le a
    show (pV k (vA a)).card ≤ _
    omega
  · show (pV k (vR : PV k)).card ≤ _
    rw [pV_root]
    simp

lemma pV_card_rk2 {v : PV k} (h : 2 ≤ rk k v) : (pV k v).card ≤ 1 := by
  rcases v with z | cc | a | u
  · simp [rk] at h
  · simp [rk] at h
  · exact pV_act_card_le a
  · show (pV k (vR : PV k)).card ≤ _
    rw [pV_root]
    simp

lemma pV_rk3 {v : PV k} (h : 3 ≤ rk k v) : pV k v = ∅ := by
  rcases v with z | cc | a | u
  · simp [rk] at h
  · simp [rk] at h
  · simp [rk] at h
  · exact pV_root

/-! ### The DAG as a `CostEngines.Dag` -/

variable (k)

/-- Number of vertices. -/
def pgN : ℕ := Fintype.card (PV k)

variable {k}

/-- Gate number of a vertex. -/
def gid (v : PV k) : ℕ := (Fintype.equivFin (PV k) v : ℕ)

lemma gid_lt (v : PV k) : gid v < pgN k := (Fintype.equivFin (PV k) v).isLt

lemma gid_injective : Function.Injective (gid (k := k)) := fun _ _ h =>
  (Fintype.equivFin (PV k)).injective (Fin.ext h)

variable (k)

/-- The vertex with a given gate number. -/
def gof (g : ℕ) (h : g < pgN k) : PV k := (Fintype.equivFin (PV k)).symm ⟨g, h⟩

variable {k}

lemma gid_gof (g : ℕ) (h : g < pgN k) : gid (gof k g h) = g := by
  simp [gid, gof]

lemma gof_gid (v : PV k) : gof k (gid v) (gid_lt v) = v := by
  simp [gid, gof]

variable (k)

/-- **The parity-grid DAG** of `thm:coded-covers`, Step 1, with explicit child and parent
lists and levels `0, …, 3`. -/
def pgDag : Dag where
  N := pgN k
  children := fun g => if h : g < pgN k then (cV k (gof k g h)).toList.map gid else []
  parents := fun g => if h : g < pgN k then (pV k (gof k g h)).toList.map gid else []
  level := fun g => if h : g < pgN k then rk k (gof k g h) else 0
  L := 3

variable {k}

lemma children_gid (v : PV k) : (pgDag k).children (gid v) = (cV k v).toList.map gid := by
  simp only [pgDag, dite_eq_left (gid_lt v), gof_gid]

lemma parents_gid (v : PV k) : (pgDag k).parents (gid v) = (pV k v).toList.map gid := by
  simp only [pgDag, dite_eq_left (gid_lt v), gof_gid]

lemma level_gid (v : PV k) : (pgDag k).level (gid v) = rk k v := by
  simp only [pgDag, dite_eq_left (gid_lt v), gof_gid]

lemma children_of_not_lt {g : ℕ} (h : ¬ g < pgN k) : (pgDag k).children g = [] := by
  simp only [pgDag, dite_eq_right h]

lemma parents_of_not_lt {g : ℕ} (h : ¬ g < pgN k) : (pgDag k).parents g = [] := by
  simp only [pgDag, dite_eq_right h]

lemma mem_children {c p : ℕ} :
    c ∈ (pgDag k).children p ↔ ∃ w v, p = gid w ∧ c = gid v ∧ PEdge k w v := by
  constructor
  · intro h
    by_cases hp : p < pgN k
    · have e := gid_gof p hp
      rw [← e, children_gid] at h
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 h
      exact ⟨gof k p hp, v, e.symm, rfl, mem_cV.1 (Finset.mem_toList.1 hv)⟩
    · rw [children_of_not_lt hp] at h
      simp at h
  · rintro ⟨w, v, rfl, rfl, h⟩
    rw [children_gid]
    exact List.mem_map.2 ⟨v, Finset.mem_toList.2 (mem_cV.2 h), rfl⟩

lemma mem_parents {c p : ℕ} :
    p ∈ (pgDag k).parents c ↔ ∃ w v, p = gid w ∧ c = gid v ∧ PEdge k w v := by
  constructor
  · intro h
    by_cases hc : c < pgN k
    · have e := gid_gof c hc
      rw [← e, parents_gid] at h
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
      exact ⟨w, gof k c hc, rfl, e.symm, mem_pV.1 (Finset.mem_toList.1 hw)⟩
    · rw [parents_of_not_lt hc] at h
      simp at h
  · rintro ⟨w, v, rfl, rfl, h⟩
    rw [parents_gid]
    exact List.mem_map.2 ⟨w, Finset.mem_toList.2 (mem_pV.2 h), rfl⟩

/-- The parity-grid DAG is well formed. -/
theorem pgDag_wf : (pgDag k).WF where
  parents_iff := fun c p => by rw [mem_parents, mem_children]
  parents_nodup := fun c => by
    by_cases hc : c < pgN k
    · rw [← gid_gof c hc, parents_gid]
      exact (Finset.nodup_toList _).map gid_injective
    · rw [parents_of_not_lt hc]
      exact List.nodup_nil
  parent_lt := fun c p h => by
    obtain ⟨w, v, rfl, rfl, -⟩ := mem_parents.1 h
    exact gid_lt w
  level_lt := fun p c h => by
    obtain ⟨w, v, rfl, rfl, he⟩ := mem_children.1 h
    rw [level_gid, level_gid]
    exact he.rk_lt
  level_le := fun g => by
    by_cases hg : g < pgN k
    · rw [← gid_gof g hg, level_gid]
      exact rk_le _
    · simp [pgDag, hg]

lemma children_length (v : PV k) : ((pgDag k).children (gid v)).length = (cV k v).card := by
  rw [children_gid, List.length_map, Finset.length_toList]

lemma parents_length (v : PV k) : ((pgDag k).parents (gid v)).length = (pV k v).card := by
  rw [parents_gid, List.length_map, Finset.length_toList]

/-- Every gate has at most `4r` children. -/
theorem pgDag_degree (p : ℕ) : ((pgDag k).children p).length ≤ 4 * 2 ^ k := by
  by_cases hp : p < pgN k
  · rw [← gid_gof p hp, children_length]
    exact cV_card_le _
  · rw [children_of_not_lt hp]
    simp

lemma children_term (z : GridTerminal k) : (pgDag k).children (gid (vT z)) = [] := by
  rw [children_gid, cV_term]
  simp

lemma mem_parents_gid {p : ℕ} {v : PV k} (h : p ∈ (pgDag k).parents (gid v)) :
    ∃ w, p = gid w ∧ PEdge k w v := by
  obtain ⟨w, v', rfl, e, he⟩ := mem_parents.1 h
  rw [← gid_injective e] at he
  exact ⟨w, rfl, he⟩

/-- **Shape bounds for `wave_cost_three_layers`.**  A terminal has at most two parents,
each of which has at most `r` parents, each of which has at most one parent, which has
none. -/
theorem pgDag_shape (z : GridTerminal k) :
    ((pgDag k).parents (gid (vT z))).length ≤ 2 ∧
    (∀ g ∈ (pgDag k).parents (gid (vT z)), ((pgDag k).parents g).length ≤ 2 ^ k) ∧
    (∀ g ∈ ((pgDag k).parents (gid (vT z))).flatMap (pgDag k).parents,
      ((pgDag k).parents g).length ≤ 1) ∧
    (∀ g ∈ (((pgDag k).parents (gid (vT z))).flatMap (pgDag k).parents).flatMap
      (pgDag k).parents, (pgDag k).parents g = []) := by
  have h1 : ∀ g ∈ (pgDag k).parents (gid (vT z)), ∃ w, g = gid w ∧ 1 ≤ rk k w := by
    intro g hg
    obtain ⟨w, rfl, he⟩ := mem_parents_gid hg
    exact ⟨w, rfl, by have := he.rk_lt; omega⟩
  have h2 : ∀ g ∈ ((pgDag k).parents (gid (vT z))).flatMap (pgDag k).parents,
      ∃ w, g = gid w ∧ 2 ≤ rk k w := by
    intro g hg
    obtain ⟨g1, hg1, hg⟩ := List.mem_flatMap.1 hg
    obtain ⟨w1, rfl, hw1⟩ := h1 g1 hg1
    obtain ⟨w, rfl, he⟩ := mem_parents_gid hg
    exact ⟨w, rfl, by have := he.rk_lt; omega⟩
  have h3 : ∀ g ∈ (((pgDag k).parents (gid (vT z))).flatMap (pgDag k).parents).flatMap
      (pgDag k).parents, ∃ w, g = gid w ∧ 3 ≤ rk k w := by
    intro g hg
    obtain ⟨g1, hg1, hg⟩ := List.mem_flatMap.1 hg
    obtain ⟨w1, rfl, hw1⟩ := h2 g1 hg1
    obtain ⟨w, rfl, he⟩ := mem_parents_gid hg
    exact ⟨w, rfl, by have := he.rk_lt; omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [parents_length]
    exact pV_term_card_le z
  · intro g hg
    obtain ⟨w, rfl, hw⟩ := h1 g hg
    rw [parents_length]
    exact pV_card_rk1 hw
  · intro g hg
    obtain ⟨w, rfl, hw⟩ := h2 g hg
    rw [parents_length]
    exact pV_card_rk2 hw
  · intro g hg
    obtain ⟨w, rfl, hw⟩ := h3 g hg
    rw [parents_gid, pV_rk3 hw]
    simp

/-! ### Size -/

variable (k)

/-- Number of edges (incidences) of the DAG. -/
def pgE : ℕ := ∑ g ∈ range (pgDag k).N, ((pgDag k).children g).length

variable {k}

/-- The DAG has `r² + 1` terminals, `2r` coordinate gates, `4(r - 1)` parity actions and the
root. -/
theorem pgN_eq : pgN k = (2 ^ k * 2 ^ k + 1) + 2 * 2 ^ k + pgD k + 1 := by
  have hm : Fintype.card (Mask k) = 2 ^ k := by
    rw [← card_univ, card_univ_mask]
  unfold pgN
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, Fintype.card_option,
    Fintype.card_prod, Fintype.card_prod, Fintype.card_bool, hm, Fintype.card_fin,
    Fintype.card_unit]
  ring

lemma pgE_eq : pgE k = ∑ v : PV k, (cV k v).card := by
  have h1 := Fin.sum_univ_eq_sum_range (fun g => ((pgDag k).children g).length) (pgN k)
  have h2 := Equiv.sum_comp (Fintype.equivFin (PV k))
    (fun i : Fin (Fintype.card (PV k)) => ((pgDag k).children (i : ℕ)).length)
  have h3 : ∑ v : PV k, ((pgDag k).children ((Fintype.equivFin (PV k) v : Fin _) : ℕ)).length
      = ∑ v : PV k, (cV k v).card := sum_congr rfl (fun v _ => children_length v)
  unfold pgE
  show ∑ g ∈ range (pgN k), _ = _
  rw [← h1, ← h3, h2]
  rfl

/-- **Edge count**: `2r² ≤ |E| ≤ 2r² + 2r d + d + 1`. -/
theorem pgE_bounds : 2 * 2 ^ k * 2 ^ k ≤ pgE k ∧
    pgE k ≤ 2 * 2 ^ k * 2 ^ k + pgD k * (2 * 2 ^ k) + pgD k + 1 := by
  have hT : ∑ z : GridTerminal k, (cV k (vT z)).card = 0 :=
    sum_eq_zero (fun z _ => by rw [cV_term]; simp)
  have hC : ∑ cc : Bool × Mask k, (cV k (vC cc)).card = 2 * 2 ^ k * 2 ^ k := by
    rw [sum_congr rfl (fun cc _ => cV_coord_card cc), sum_const, card_univ, Fintype.card_prod,
      Fintype.card_bool, ← card_univ, card_univ_mask, smul_eq_mul]
  have hA : ∑ a : Fin (pgD k), (cV k (vA a)).card ≤ pgD k * (2 * 2 ^ k) := by
    calc ∑ a : Fin (pgD k), (cV k (vA a)).card ≤ ∑ _a : Fin (pgD k), 2 * 2 ^ k :=
          sum_le_sum (fun a _ => cV_act_card_le a)
      _ = pgD k * (2 * 2 ^ k) := by simp
  have hR := cV_root_card_le (k := k)
  have hsum : pgE k = ∑ z : GridTerminal k, (cV k (vT z)).card
      + (∑ cc : Bool × Mask k, (cV k (vC cc)).card
        + (∑ a : Fin (pgD k), (cV k (vA a)).card + (cV k (vR : PV k)).card)) := by
    rw [pgE_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp
  rw [hsum, hT, hC]
  constructor <;> omega

/-- **`Θ(r²)` size.**  `r² ≤ |V| ≤ 7 r²` and `2 r² ≤ |E| ≤ 11 r²`. -/
theorem pgDag_size : 2 ^ k * 2 ^ k ≤ (pgDag k).N ∧ (pgDag k).N ≤ 7 * (2 ^ k * 2 ^ k) ∧
    2 * (2 ^ k * 2 ^ k) ≤ pgE k ∧ pgE k ≤ 11 * (2 ^ k * 2 ^ k) := by
  have hN : (pgDag k).N = pgN k := rfl
  have hr := one_le_r (k := k)
  have hd := pgD_le (k := k)
  obtain ⟨hE1, hE2⟩ := pgE_bounds (k := k)
  rw [hN, pgN_eq]
  generalize 2 ^ k = r at *
  generalize pgD k = d at *
  have hd' : d ≤ 4 * r := by omega
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

end Graph

/-! ## Root supports, their distinctness, and the unique `ε`-optimal action -/

section Supports

variable (k : ℕ)

/-- Terminal support of a root action: actions `0, …, d - 1` are the parity actions,
action `d` (`Fin.last`) is the direct terminal `w*`. -/
def pgSupp (a : Fin (pgD k + 1)) : Finset (GridTerminal k) :=
  Fin.lastCases (motive := fun _ => Finset (GridTerminal k)) {none}
    (fun i => paritySupp (pgIdx k i)) a

/-- The vertex of a root action. -/
def pgGate (a : Fin (pgD k + 1)) : PV k :=
  Fin.lastCases (motive := fun _ => PV k) (vT none) (fun i => vA i) a

/-- Mean rewards: `0.99` for `w*`, `0.02` for every grid terminal. -/
def pgMean : GridTerminal k → ℝ
  | none => 0.99
  | some _ => 0.02

variable {k}

@[simp] lemma pgSupp_last : pgSupp k (Fin.last _) = {none} := by
  simp [pgSupp]

@[simp] lemma pgSupp_castSucc (i : Fin (pgD k)) :
    pgSupp k i.castSucc = paritySupp (pgIdx k i) := by
  simp [pgSupp]

@[simp] lemma pgGate_last : pgGate k (Fin.last _) = vT none := by
  simp [pgGate]

@[simp] lemma pgGate_castSucc (i : Fin (pgD k)) : pgGate k i.castSucc = vA i := by
  simp [pgGate]

lemma none_notMem_paritySupp (p : ParityIndex k) : (none : GridTerminal k) ∉ paritySupp p := by
  simp [paritySupp, parityMem]

lemma some_mem_paritySupp (p : ParityIndex k) (x : Mask k × Mask k) :
    some x ∈ paritySupp p ↔ p.2.1 ⬝ᵥ (if p.1 then x.1 else x.2) = p.2.2 := by
  simp [paritySupp, parityMem]

lemma pEdge_act_coord_iff (a : Fin (pgD k)) (cc : Bool × Mask k) :
    PEdge k (vA a) (vC cc) ↔
      (pgIdx k a).1 = cc.1 ∧ (pgIdx k a).2.1 ⬝ᵥ cc.2 = (pgIdx k a).2.2 := by
  constructor
  · intro h
    obtain ⟨cc', e, h'⟩ := h.of_parent_act
    have e' : cc = cc' := Sum.inl_injective (Sum.inr_injective e)
    subst e'
    exact h'
  · exact fun h => pEdge_act_coord a cc h.1 h.2

lemma pEdge_coord_term_iff (cc : Bool × Mask k) (z : GridTerminal k) :
    PEdge k (vC cc) (vT z) ↔ ∃ x, z = some x ∧ (if cc.1 then x.1 else x.2) = cc.2 := by
  constructor
  · intro h
    obtain ⟨x, e, h'⟩ := h.of_parent_coord
    exact ⟨x, Sum.inl_injective e, h'⟩
  · rintro ⟨x, rfl, h⟩
    exact pEdge_coord_term cc x h

/-- **The root supports of the DAG are the parity supports.**  A terminal lies below the
parity action `i` (through a coordinate gate) exactly when it belongs to
`paritySupp (pgIdx k i)`, the support used in the every-layout lower bound. -/
theorem pg_action_support (i : Fin (pgD k)) (z : GridTerminal k) :
    (∃ cc, PEdge k (vA i) (vC cc) ∧ PEdge k (vC cc) (vT z)) ↔ z ∈ paritySupp (pgIdx k i) := by
  rcases z with _ | x
  · constructor
    · rintro ⟨cc, -, h2⟩
      obtain ⟨x, e, -⟩ := (pEdge_coord_term_iff cc none).1 h2
      simp at e
    · intro h
      exact absurd h (none_notMem_paritySupp _)
  · rw [some_mem_paritySupp]
    constructor
    · rintro ⟨cc, h1, h2⟩
      obtain ⟨hf, hb⟩ := (pEdge_act_coord_iff i cc).1 h1
      obtain ⟨y, e, hy⟩ := (pEdge_coord_term_iff cc (some x)).1 h2
      have e' : x = y := Option.some_injective _ e
      subst e'
      rw [hf, hy]
      exact hb
    · intro h
      exact ⟨((pgIdx k i).1, if (pgIdx k i).1 then x.1 else x.2),
        (pEdge_act_coord_iff i _).2 ⟨rfl, h⟩, (pEdge_coord_term_iff _ _).2 ⟨x, rfl, rfl⟩⟩

/-- The only terminal below the root action `w*` is `w*` itself (it is a terminal). -/
theorem pg_win_support (c : PV k) : ¬ PEdge k (vT (none : GridTerminal k)) c :=
  fun h => h.not_parent_term

lemma zmod2_iff : ∀ u v b b' : ZMod 2, (u = b ↔ v = b') → u + b = v + b' := by decide

lemma zmod2_ne : ∀ c b : ZMod 2, c ≠ 0 → ¬ (0 = b ↔ c = b) := by decide

lemma zmod2_one : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide

lemma parity_cross_ne {a a' : Mask k} {b b' : ZMod 2} (ha : a ≠ 0) :
    ¬ ∀ u v : Mask k, (a ⬝ᵥ u = b ↔ a' ⬝ᵥ v = b') := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
  have h0 := h 0 0
  have h1 := h (Pi.single i 1) 0
  rw [dotProduct_single_one] at h1
  simp only [dotProduct_zero] at h0 h1
  exact zmod2_ne (a i) b (by simpa using hi) (h0.trans h1.symm)

lemma parity_same_eq {a a' : Mask k} {b b' : ZMod 2}
    (h : ∀ v : Mask k, (a ⬝ᵥ v = b ↔ a' ⬝ᵥ v = b')) : a = a' ∧ b = b' := by
  have key : ∀ v, a ⬝ᵥ v + b = a' ⬝ᵥ v + b' := fun v => zmod2_iff _ _ _ _ (h v)
  have hb : b = b' := by simpa using key 0
  refine ⟨?_, hb⟩
  funext i
  have := key (Pi.single i 1)
  rw [dotProduct_single_one, dotProduct_single_one, hb] at this
  exact add_right_cancel this

/-- **Distinct parity supports.**  Different parity actions have different supports. -/
theorem paritySupp_injOn {p q : ParityIndex k} (hp : p ∈ parityActions k)
    (hq : q ∈ parityActions k) (h : paritySupp p = paritySupp q) : p = q := by
  obtain ⟨f, a, b⟩ := p
  obtain ⟨f', a', b'⟩ := q
  have ha : a ≠ 0 := by simpa [parityActions] using hp
  have ha' : a' ≠ 0 := by simpa [parityActions] using hq
  have hx : ∀ x : Mask k × Mask k, (a ⬝ᵥ (if f then x.1 else x.2) = b ↔
      a' ⬝ᵥ (if f' then x.1 else x.2) = b') := by
    intro x
    have := Finset.ext_iff.1 h (some x)
    rwa [some_mem_paritySupp, some_mem_paritySupp] at this
  cases f <;> cases f'
  · obtain ⟨rfl, rfl⟩ := parity_same_eq (a := a) (a' := a') (b := b) (b' := b')
      (fun v => by simpa using hx (v, v))
    rfl
  · exact absurd (fun u v => by simpa using hx (v, u))
      (parity_cross_ne (a := a) (a' := a') (b := b) (b' := b') ha)
  · exact absurd (fun u v => by simpa using hx (u, v))
      (parity_cross_ne (a := a) (a' := a') (b := b) (b' := b') ha)
  · obtain ⟨rfl, rfl⟩ := parity_same_eq (a := a) (a' := a') (b := b) (b' := b')
      (fun v => by simpa using hx (v, v))
    rfl

lemma paritySupp_nonempty {p : ParityIndex k} (hp : p ∈ parityActions k) :
    (paritySupp p).Nonempty := by
  obtain ⟨f, a, b⟩ := p
  have ha : a ≠ 0 := by simpa [parityActions] using hp
  obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
  have hi1 : a i = 1 := zmod2_one _ (by simpa using hi)
  refine ⟨some (Pi.single i b, Pi.single i b), ?_⟩
  rw [some_mem_paritySupp]
  cases f <;> simp [dotProduct_single, hi1]

lemma pgSupp_nonempty (a : Fin (pgD k + 1)) : (pgSupp k a).Nonempty := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
  · rw [pgSupp_castSucc]
    exact paritySupp_nonempty (pgIdx_mem k i)
  · rw [pgSupp_last]
    exact singleton_nonempty _

/-- **The `d + 1` root supports are pairwise distinct.** -/
theorem pgSupp_injective : Function.Injective (pgSupp k) := by
  intro a a' h
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last a' with ⟨i', rfl⟩ | rfl
  · rw [pgSupp_castSucc, pgSupp_castSucc] at h
    rw [pgIdx_injective k (paritySupp_injOn (pgIdx_mem k i) (pgIdx_mem k i') h)]
  · rw [pgSupp_castSucc, pgSupp_last] at h
    have : (none : GridTerminal k) ∈ paritySupp (pgIdx k i) := by
      rw [h]
      exact mem_singleton_self _
    exact absurd this (none_notMem_paritySupp _)
  · rw [pgSupp_castSucc, pgSupp_last] at h
    have : (none : GridTerminal k) ∈ paritySupp (pgIdx k i') := by
      rw [← h]
      exact mem_singleton_self _
    exact absurd this (none_notMem_paritySupp _)
  · rfl

lemma gmax_pgMean : gmax (pgMean k) = 0.99 := by
  unfold gmax
  apply le_antisymm
  · apply Finset.sup'_le
    intro z _
    rcases z with _ | x
    · exact le_rfl
    · show (0.02 : ℝ) ≤ 0.99
      norm_num
  · exact Finset.le_sup' (pgMean k) (mem_univ none)

/-- **Reward gaps.**  The root action `w*` has regret `0`; every parity action has regret
`0.97`. -/
theorem pg_regret (a : Fin (pgD k + 1)) (hne : (pgSupp k a).Nonempty) :
    regret (pgSupp k a) hne (pgMean k) = if a = Fin.last _ then 0 else 0.97 := by
  have hval : ∀ (S : Finset (GridTerminal k)) (hS : S.Nonempty) (c : ℝ),
      (∀ z ∈ S, pgMean k z = c) → val S hS (pgMean k) = c := by
    intro S hS c hc
    unfold val
    obtain ⟨z, hz⟩ := hS
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun y hy => (hc y hy).le)
    · rw [← hc z hz]
      exact Finset.le_sup' _ hz
  unfold regret
  rw [gmax_pgMean]
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
  · rw [hval _ hne 0.02, ite_eq_right (Fin.castSucc_lt_last i).ne]
    · norm_num
    · intro z hz
      rw [pgSupp_castSucc] at hz
      rcases z with _ | x
      · exact absurd hz (none_notMem_paritySupp _)
      · rfl
  · rw [hval _ hne 0.99, ite_eq_left rfl]
    · norm_num
    · intro z hz
      rw [pgSupp_last, mem_singleton] at hz
      rw [hz]
      rfl

/-- **`w*` is the unique `ε`-optimal root action at `ε = 1/5`.** -/
theorem pg_unique_optimal (a : Fin (pgD k + 1)) (hne : (pgSupp k a).Nonempty) :
    regret (pgSupp k a) hne (pgMean k) ≤ 1 / 5 ↔ a = Fin.last _ := by
  rw [pg_regret]
  constructor
  · intro h
    by_contra ha
    rw [ite_eq_right ha] at h
    norm_num at h
  · intro ha
    rw [ite_eq_left ha]
    norm_num

end Supports

/-! ## Step 3a: the search process and the root-level selection inequality -/

section Search

variable {k : ℕ}

/-- The reward ranges of `thm:coded-covers`: every observation of `w*` lies in
`[0.98, 1]`, every observation of a grid terminal in `[0.01, 0.03]`. -/
structure PGTape (x : GridTerminal k → ℕ → ℝ) : Prop where
  win : ∀ i, x none i ∈ Set.Icc (0.98 : ℝ) 1
  grid : ∀ g i, x (some g) i ∈ Set.Icc (0.01 : ℝ) 0.03

/-- Reward observed by rollout `s`: the next unread entry of the tape of the terminal
reached. -/
def pgReward (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (s : ℕ) : ℝ :=
  x (zt s) (queryCount zt s (zt s))

/-- Empirical mean return of root action `a` before rollout `t`. -/
def pgQ (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1)) (zt : ℕ → GridTerminal k)
    (t : ℕ) (a : Fin (pgD k + 1)) : ℝ :=
  (∑ s ∈ (range t).filter (fun s => sel s = a), pgReward x zt s) / uctCount sel t a

/-- **A UCT search (`c = 2`) on the parity-grid DAG with rewards read from the tapes `x`.**
`sel s` is the root action of rollout `s`; `zt s` is the terminal reached, any terminal of
the support of `sel s` (the selections below the root are arbitrary, in particular
recursive UCT with any tie-breaking); the root is a UCT node whose empirical means are the
averages of the observed rewards. -/
structure ParitySearch (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) : Prop where
  reach : ∀ s, zt s ∈ pgSupp k (sel s)
  uct : UCTRun 2 (pgQ x sel zt) sel

variable {x : GridTerminal k → ℕ → ℝ} {sel : ℕ → Fin (pgD k + 1)} {zt : ℕ → GridTerminal k}

/-- `w*` is observed exactly when the root action `w*` is selected. -/
lemma ParitySearch.zt_none_iff (h : ParitySearch x sel zt) (s : ℕ) :
    zt s = none ↔ sel s = Fin.last _ := by
  have hr := h.reach s
  rcases Fin.eq_castSucc_or_eq_last (sel s) with ⟨i, hi⟩ | hl
  · rw [hi, pgSupp_castSucc] at hr
    constructor
    · intro hz
      rw [hz] at hr
      exact absurd hr (none_notMem_paritySupp _)
    · intro hs
      rw [hi] at hs
      exact absurd hs (Fin.castSucc_lt_last i).ne
  · rw [hl, pgSupp_last] at hr
    exact ⟨fun _ => hl, fun _ => mem_singleton.1 hr⟩

lemma ParitySearch.reward_win (h : ParitySearch x sel zt) (hx : PGTape x) {s : ℕ}
    (hs : sel s = Fin.last _) : 0.98 ≤ pgReward x zt s := by
  unfold pgReward
  rw [(h.zt_none_iff s).2 hs]
  exact (hx.win _).1

lemma ParitySearch.reward_lose (h : ParitySearch x sel zt) (hx : PGTape x) {s : ℕ}
    (hs : sel s ≠ Fin.last _) : pgReward x zt s ≤ 0.03 := by
  unfold pgReward
  have hz : zt s ≠ none := fun e => hs ((h.zt_none_iff s).1 e)
  obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hz
  rw [hg]
  exact (hx.grid g _).2

lemma ParitySearch.Q_win (h : ParitySearch x sel zt) (hx : PGTape x) {t : ℕ}
    (hpos : 1 ≤ uctCount sel t (Fin.last (pgD k))) :
    0.98 ≤ pgQ x sel zt t (Fin.last (pgD k)) := by
  unfold pgQ
  have hc : (0 : ℝ) < uctCount sel t (Fin.last (pgD k)) := by exact_mod_cast hpos
  rw [le_div_iff₀ hc]
  have := Finset.card_nsmul_le_sum ((range t).filter (fun s => sel s = Fin.last (pgD k)))
    (pgReward x zt) 0.98 (fun s hs => h.reward_win hx (mem_filter.1 hs).2)
  rw [nsmul_eq_mul] at this
  rw [mul_comm]
  exact this

lemma ParitySearch.Q_lose (h : ParitySearch x sel zt) (hx : PGTape x) (t : ℕ)
    {a : Fin (pgD k + 1)} (ha : a ≠ Fin.last _) : pgQ x sel zt t a ≤ 0.03 := by
  unfold pgQ
  rcases Nat.eq_zero_or_pos (uctCount sel t a) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero]
    norm_num
  · have hc : (0 : ℝ) < uctCount sel t a := by exact_mod_cast hpos
    rw [div_le_iff₀ hc]
    have := Finset.sum_le_card_nsmul ((range t).filter (fun s => sel s = a))
      (pgReward x zt) 0.03
      (fun s hs => h.reward_lose hx (by rw [(mem_filter.1 hs).2]; exact ha))
    rw [nsmul_eq_mul] at this
    rw [mul_comm]
    exact this

/-- **The root-level selection inequality** (hypothesis `hsel` of
`CostEngines.winner_count_lower` and `CostEngines.parity_total_work`), derived from the
reward ranges: after the `d + 1` forced rollouts, a parity action is selected at rollout
`t` only if `0.03 + 2 √(log (1 + t) / N_a(t)) ≥ 0.98`. -/
theorem ParitySearch.selection_ineq (h : ParitySearch x sel zt) (hx : PGTape x)
    (i : Fin (pgD k)) {t : ℕ} (ht : pgD k + 1 ≤ t) (hp : sel t = i.castSucc) :
    (0.98 : ℝ) ≤ 0.03 + 2 * Real.sqrt (Real.log (1 + t) / uctCount sel t i.castSucc) := by
  have hcard : Fintype.card (Fin (pgD k + 1)) ≤ t := by
    rw [Fintype.card_fin]
    exact ht
  have hg := h.uct.greedy t hcard (Fin.last _)
  rw [hp] at hg
  unfold uctIndex at hg
  have h1 := h.Q_win hx (h.uct.one_le (Fin.last _) hcard)
  have h2 := h.Q_lose hx t (a := i.castSucc) (Fin.castSucc_lt_last i).ne
  have h3 : 0 ≤ 2 * Real.sqrt (Real.log (1 + (t : ℝ)) /
      (uctCount sel t (Fin.last (pgD k)) : ℝ)) := by positivity
  linarith

/-- **Count of the winning action** (`CostEngines.winner_count_lower` with its hypotheses
discharged): `N_{w*}(t) ≥ t - d (1 + 5 log (1 + t))` for `t ≥ d + 1`. -/
theorem ParitySearch.win_count_ge (h : ParitySearch x sel zt) (hx : PGTape x) {t : ℕ}
    (ht : pgD k + 1 ≤ t) :
    (t : ℝ) - pgD k * (1 + 5 * Real.log (1 + t)) ≤ uctCount sel t (Fin.last (pgD k)) := by
  refine winner_count_lower (d := pgD k) (fun a t => uctCount sel t a.castSucc)
    (fun t => uctCount sel t (Fin.last _)) (fun a t => sel t = a.castSucc) (pgD k + 1)
    ?_ ?_ ?_ ?_ t ht
  · intro t
    have := uctCount_sum sel t
    rw [Fin.sum_univ_castSucc] at this
    show uctCount sel t (Fin.last _) + ∑ a : Fin (pgD k), uctCount sel t a.castSucc = t
    rw [add_comm]
    exact this
  · intro a t _
    constructor
    · intro hp
      show uctCount sel (t + 1) a.castSucc = uctCount sel t a.castSucc + 1
      rw [uctCount_succ, ite_eq_left hp]
    · intro hp
      show uctCount sel (t + 1) a.castSucc = uctCount sel t a.castSucc
      rw [uctCount_succ, ite_eq_right hp, add_zero]
  · intro a t ht hp
    exact h.selection_ineq hx a ht hp
  · intro a
    have := h.uct.forced a.castSucc
    rw [Fintype.card_fin] at this
    exact this.le

/-- **Searches exist** for every tape and every rule `ρ` choosing the terminal reached
below a parity action: the model is not vacuous. -/
theorem exists_paritySearch (x : GridTerminal k → ℕ → ℝ)
    (ρ : ℕ → Fin (pgD k) → GridTerminal k) (hρ : ∀ s i, ρ s i ∈ paritySupp (pgIdx k i)) :
    ∃ sel zt, ParitySearch x sel zt := by
  let ztOf : (ℕ → Fin (pgD k + 1)) → ℕ → GridTerminal k :=
    fun sel s => Fin.lastCases (motive := fun _ => GridTerminal k) none (fun i => ρ s i) (sel s)
  have hloc : ∀ (sel sel' : ℕ → Fin (pgD k + 1)) (t : ℕ), (∀ s, s < t → sel s = sel' s) →
      ∀ s, s < t → ztOf sel s = ztOf sel' s := by
    intro sel sel' t hss s hs
    show Fin.lastCases (motive := fun _ => GridTerminal k) none (fun i => ρ s i) (sel s)
      = Fin.lastCases (motive := fun _ => GridTerminal k) none (fun i => ρ s i) (sel' s)
    rw [hss s hs]
  obtain ⟨sel, hsel⟩ := exists_uctRun (ι := Fin (pgD k + 1)) 2
    (fun sel t a => pgQ x sel (ztOf sel) t a)
    (by
      intro sel sel' t hss
      funext a
      have hf : (range t).filter (fun s => sel s = a) = (range t).filter (fun s => sel' s = a) :=
        Finset.filter_congr (fun s hs => by rw [hss s (mem_range.mp hs)])
      have hc : uctCount sel t a = uctCount sel' t a := by
        unfold uctCount
        rw [hf]
      show (∑ s ∈ (range t).filter (fun s => sel s = a), pgReward x (ztOf sel) s)
          / (uctCount sel t a : ℝ)
        = (∑ s ∈ (range t).filter (fun s => sel' s = a), pgReward x (ztOf sel') s)
          / (uctCount sel' t a : ℝ)
      rw [hc, hf]
      congr 1
      refine Finset.sum_congr rfl (fun s hs => ?_)
      have hs' : s < t := mem_range.mp (Finset.mem_filter.mp hs).1
      have hz := hloc sel sel' t hss s hs'
      have hq : queryCount (ztOf sel) s (ztOf sel s) = queryCount (ztOf sel') s (ztOf sel s) := by
        unfold queryCount
        congr 1
        refine Finset.filter_congr (fun s' hs'' => ?_)
        rw [hloc sel sel' t hss s' (lt_trans (mem_range.mp hs'') hs')]
      show x (ztOf sel s) (queryCount (ztOf sel) s (ztOf sel s))
        = x (ztOf sel' s) (queryCount (ztOf sel') s (ztOf sel' s))
      rw [hq, hz])
  refine ⟨sel, ztOf sel, ⟨fun s => ?_, hsel⟩⟩
  show Fin.lastCases (motive := fun _ => GridTerminal k) none (fun i => ρ s i) (sel s)
    ∈ pgSupp k (sel s)
  rcases Fin.eq_castSucc_or_eq_last (sel s) with ⟨i, hi⟩ | hl
  · rw [hi, Fin.lastCases_castSucc, pgSupp_castSucc]
    exact hρ s i
  · rw [hl, Fin.lastCases_last, pgSupp_last]
    exact mem_singleton_self _

end Search

/-! ## Step 3b: the monitor (interval engine on the DAG) and its stopping test -/

section Monitor

variable {k : ℕ}

/-- Number of terminals `M = r² + 1`, used in the Hoeffding radius. -/
def pgM (k : ℕ) : ℝ := ((2 ^ k * 2 ^ k + 1 : ℕ) : ℝ)

/-- Terminal table after `t` rollouts: the running Hoeffding box of every terminal. -/
def pgTab (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (z : GridTerminal k) : NNReal × NNReal :=
  ((tapeLo (pgM k) δ x zt t z).toNNReal, (tapeHi (pgM k) δ x zt t z).toNNReal)

/-- Terminal update delivered to the engine after rollout `t - 1` (`t ≥ 1`). -/
def pgUpd (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    ℕ × NNReal × NNReal :=
  (gid (vT (zt (t - 1))), (pgTab δ x zt t (zt (t - 1))).1, (pgTab δ x zt t (zt (t - 1))).2)

/-- Initial engine state: every lower endpoint `0`, every upper endpoint `1`. -/
def pgInit (_k : ℕ) : EState NNReal × EState NNReal :=
  (⟨fun _ => ⊥, fun _ _ => ⊥⟩, ⟨fun _ => 1, fun _ _ => 1⟩)

/-- Engine state after `t` rollouts (one interval wave per rollout). -/
def pgState (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    EState NNReal × EState NNReal :=
  runState (pgDag k) (pgUpd δ x zt) (pgInit k) t

lemma ivWave_fst {G : Dag} (g : ℕ) (yl yu : NNReal) (s : EState NNReal × EState NNReal) :
    (ivWave G g yl yu s).1 = ((wave G g yl s.1).1, (wave G g yu s.2).1) := rfl

lemma waveCost_succ {G : Dag} (u : ℕ → ℕ × NNReal × NNReal)
    (s0 : EState NNReal × EState NNReal) (t : ℕ) :
    waveCost G u s0 (t + 1)
      = (ivWave G (u (t + 1)).1 (u (t + 1)).2.1 (u (t + 1)).2.2 (runState G u s0 t)).2 := rfl

lemma pgUpd_succ (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    pgUpd δ x zt (t + 1)
      = (gid (vT (zt t)), (pgTab δ x zt (t + 1) (zt t)).1, (pgTab δ x zt (t + 1) (zt t)).2) := by
  simp only [pgUpd, Nat.add_sub_cancel]

lemma pgState_succ (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    pgState δ x zt (t + 1)
      = (ivWave (pgDag k) (gid (vT (zt t))) (pgTab δ x zt (t + 1) (zt t)).1
          (pgTab δ x zt (t + 1) (zt t)).2 (pgState δ x zt t)).1 := by
  show (ivWave (pgDag k) (pgUpd δ x zt (t + 1)).1 (pgUpd δ x zt (t + 1)).2.1
    (pgUpd δ x zt (t + 1)).2.2 (pgState δ x zt t)).1 = _
  rw [pgUpd_succ]

lemma heapMax_const (cs : List ℕ) (y : NNReal) (h : cs ≠ []) :
    heapMax cs (fun _ => y) = y := by
  unfold heapMax
  induction cs with
  | nil => exact absurd rfl h
  | cons c cs ih =>
    by_cases hc : cs = []
    · subst hc
      simp
    · simp only [List.map_cons, List.foldr_cons]
      rw [ih hc]
      exact sup_idem _

lemma heapMax_le {cs : List ℕ} {key : ℕ → NNReal} {y : NNReal} (h : ∀ c ∈ cs, key c ≤ y) :
    heapMax cs key ≤ y := by
  unfold heapMax
  induction cs with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact sup_le (h c (List.mem_cons.2 (Or.inl rfl)))
      (ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc')))

/-- If every leaf of a child-closed set of gates stores at most `c0`, so does every gate
of the set. -/
lemma inv_val_le {G : Dag} (hG : G.WF) {s : EState NNReal} (h : Inv G s) (U : ℕ → Prop)
    (hU : ∀ g, U g → ∀ c ∈ G.children g, U c) (c0 : NNReal)
    (hleaf : ∀ g, U g → G.children g = [] → s.val g ≤ c0) : ∀ g, U g → s.val g ≤ c0 := by
  have key : ∀ n g, G.level g < n → U g → s.val g ≤ c0 := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg hUg
      by_cases hl : G.children g = []
      · exact hleaf g hUg hl
      · rw [h.gate g hl]
        apply heapMax_le
        intro c hc
        rw [h.keys g c hc]
        have := hG.level_lt g c hc
        exact ih c (by omega) (hU g hUg c hc)
  exact fun g hg => key (G.level g + 1) g (Nat.lt_succ_self _) hg

lemma pgInit_inv : Inv (pgDag k) (pgInit k).1 ∧ Inv (pgDag k) (pgInit k).2 :=
  ⟨Inv.bot _, ⟨fun _ hg => (heapMax_const _ 1 hg).symm, fun _ _ _ => rfl⟩⟩

lemma pgUpd_lt (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    (pgUpd δ x zt t).1 < (pgDag k).N := gid_lt _

/-- The engine invariant holds at every time: the stored endpoints of every gate are the
exact maxima over its children. -/
theorem pgState_inv (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    Inv (pgDag k) (pgState δ x zt t).1 ∧ Inv (pgDag k) (pgState δ x zt t).2 :=
  runState_inv pgDag_wf _ (pgUpd_lt δ x zt) _ pgInit_inv t

/-! ### Facts about the Hoeffding boxes -/

lemma queryCount_succ' (zt : ℕ → GridTerminal k) (t : ℕ) (z : GridTerminal k) :
    queryCount zt (t + 1) z = queryCount zt t z + if zt t = z then 1 else 0 :=
  uctCount_succ zt t z

lemma hw_nonneg (M δ y : ℝ) : 0 ≤ hoeffdingWidth M δ y := by
  unfold hoeffdingWidth
  positivity

lemma runLo_le {lo : ℕ → ℝ} {c : ℝ} : ∀ n, (∀ j ≤ n, lo j ≤ c) → runLo lo n ≤ c
  | 0, h => h 0 le_rfl
  | n + 1, h => max_le (runLo_le n (fun j hj => h j (Nat.le_succ_of_le hj))) (h (n + 1) le_rfl)

lemma le_runHi {hi : ℕ → ℝ} {c : ℝ} : ∀ n, (∀ j ≤ n, c ≤ hi j) → c ≤ runHi hi n
  | 0, h => h 0 le_rfl
  | n + 1, h => le_min (le_runHi n (fun j hj => h j (Nat.le_succ_of_le hj))) (h (n + 1) le_rfl)

lemma le_runLo_self (lo : ℕ → ℝ) (n : ℕ) : lo n ≤ runLo lo n := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

lemma emp_le {y : ℕ → ℝ} {c : ℝ} (h : ∀ i, y i ≤ c) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ range n, y i) / n ≤ c := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [div_le_iff₀ hn']
  have := Finset.sum_le_card_nsmul (range n) y c (fun i _ => h i)
  rw [card_range, nsmul_eq_mul] at this
  linarith

lemma le_emp {y : ℕ → ℝ} {c : ℝ} (h : ∀ i, c ≤ y i) {n : ℕ} (hn : n ≠ 0) :
    c ≤ (∑ i ∈ range n, y i) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [le_div_iff₀ hn']
  have := Finset.card_nsmul_le_sum (range n) y c (fun i _ => h i)
  rw [card_range, nsmul_eq_mul] at this
  linarith

lemma tapeLo_nonneg (M δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (z : GridTerminal k) : 0 ≤ tapeLo M δ x zt t z := by
  unfold tapeLo
  have h0 : runLo (hoeffLo M δ (x z)) 0 = 0 := by simp [runLo, hoeffLo]
  calc (0 : ℝ) = runLo (hoeffLo M δ (x z)) 0 := h0.symm
    _ ≤ _ := runLo_mono _ (Nat.zero_le _)

lemma tapeHi_le_one (M δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (z : GridTerminal k) : tapeHi M δ x zt t z ≤ 1 := by
  unfold tapeHi
  have h0 : runHi (hoeffHi M δ (x z)) 0 = 1 := by simp [runHi, hoeffHi]
  calc runHi (hoeffHi M δ (x z)) (queryCount zt t z) ≤ runHi (hoeffHi M δ (x z)) 0 :=
        runHi_anti _ (Nat.zero_le _)
    _ = 1 := h0

variable {x : GridTerminal k → ℕ → ℝ}

/-- The lower endpoint of a grid terminal never exceeds `0.03`. -/
lemma tapeLo_grid (hx : PGTape x) (M δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (g : Mask k × Mask k) : tapeLo M δ x zt t (some g) ≤ 0.03 := by
  unfold tapeLo
  apply runLo_le
  intro j _
  unfold hoeffLo
  split_ifs with hj
  · norm_num
  · have h1 := emp_le (y := x (some g)) (c := 0.03) (fun i => (hx.grid g i).2) hj
    have h2 := hw_nonneg M δ j
    linarith

/-- The upper endpoint of `w*` is always at least `0.98`. -/
lemma tapeHi_win (hx : PGTape x) (M δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    0.98 ≤ tapeHi M δ x zt t none := by
  unfold tapeHi
  apply le_runHi
  intro j _
  unfold hoeffHi
  split_ifs with hj
  · norm_num
  · have h1 := le_emp (y := x none) (c := 0.98) (fun i => (hx.win i).1) hj
    have h2 := hw_nonneg M δ j
    linarith

/-- After `n ≥ 1` observations the lower endpoint of `w*` is at least `0.98 - β(n)`. -/
lemma tapeLo_win (hx : PGTape x) (M δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (hn : queryCount zt t none ≠ 0) :
    0.98 - hoeffdingWidth M δ (queryCount zt t none) / 2 ≤ tapeLo M δ x zt t none := by
  unfold tapeLo
  refine le_trans ?_ (le_runLo_self _ _)
  unfold hoeffLo
  rw [ite_eq_right hn]
  have h1 := le_emp (y := x none) (c := 0.98) (fun i => (hx.win i).1) hn
  linarith

lemma pgTab_succ_of_ne (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    {z : GridTerminal k} (hz : z ≠ zt t) : pgTab δ x zt (t + 1) z = pgTab δ x zt t z := by
  unfold pgTab tapeLo tapeHi
  rw [queryCount_succ', ite_eq_right (Ne.symm hz), add_zero]

/-- **Leaves of the engine state.**  After `t` rollouts every terminal vertex stores its
current Hoeffding box; every leaf other than `w*` has lower endpoint at most `0.03`, and
every leaf has upper endpoint at most `1`. -/
theorem pgState_leaves (hx : PGTape x) (δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    (∀ z, (pgState δ x zt t).1.val (gid (vT z)) = (pgTab δ x zt t z).1) ∧
    (∀ z, (pgState δ x zt t).2.val (gid (vT z)) = (pgTab δ x zt t z).2) ∧
    (∀ g, (pgDag k).children g = [] → g ≠ gid (vT (none : GridTerminal k)) →
      (pgState δ x zt t).1.val g ≤ Real.toNNReal 0.03) ∧
    (∀ g, (pgDag k).children g = [] → (pgState δ x zt t).2.val g ≤ 1) := by
  induction t with
  | zero =>
    refine ⟨fun z => ?_, fun z => ?_, fun g _ _ => bot_le, fun g _ => le_rfl⟩
    · have h0 : tapeLo (pgM k) δ x zt 0 z = 0 := by simp [tapeLo, queryCount, runLo, hoeffLo]
      show (⊥ : NNReal) = Real.toNNReal (tapeLo (pgM k) δ x zt 0 z)
      rw [h0, Real.toNNReal_zero]
      exact bot_eq_zero
    · have h0 : tapeHi (pgM k) δ x zt 0 z = 1 := by simp [tapeHi, queryCount, runHi, hoeffHi]
      show (1 : NNReal) = Real.toNNReal (tapeHi (pgM k) δ x zt 0 z)
      rw [h0, Real.toNNReal_one]
  | succ t ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    have hinv := pgState_inv δ x zt t
    have hs1 : (pgState δ x zt (t + 1)).1 = (wave (pgDag k) (gid (vT (zt t)))
        (pgTab δ x zt (t + 1) (zt t)).1 (pgState δ x zt t).1).1 := by
      rw [pgState_succ, ivWave_fst]
    have hs2 : (pgState δ x zt (t + 1)).2 = (wave (pgDag k) (gid (vT (zt t)))
        (pgTab δ x zt (t + 1) (zt t)).2 (pgState δ x zt t).2).1 := by
      rw [pgState_succ, ivWave_fst]
    obtain ⟨-, hy1, ho1, -⟩ := wave_spec pgDag_wf (gid (vT (zt t)))
      (pgTab δ x zt (t + 1) (zt t)).1 (pgState δ x zt t).1 (gid_lt _) hinv.1
    obtain ⟨-, hy2, ho2, -⟩ := wave_spec pgDag_wf (gid (vT (zt t)))
      (pgTab δ x zt (t + 1) (zt t)).2 (pgState δ x zt t).2 (gid_lt _) hinv.2
    rw [hs1, hs2]
    refine ⟨fun z => ?_, fun z => ?_, fun g hg hne => ?_, fun g hg => ?_⟩
    · by_cases hz : z = zt t
      · rw [hz]
        exact hy1 (children_term _)
      · rw [ho1 _ (children_term z) (fun e => hz (Sum.inl_injective (gid_injective e))), ih1,
          pgTab_succ_of_ne δ x zt t hz]
    · by_cases hz : z = zt t
      · rw [hz]
        exact hy2 (children_term _)
      · rw [ho2 _ (children_term z) (fun e => hz (Sum.inl_injective (gid_injective e))), ih2,
          pgTab_succ_of_ne δ x zt t hz]
    · by_cases hgx : g = gid (vT (zt t))
      · rw [hgx, hy1 (children_term _)]
        have hz : zt t ≠ none := fun e => hne (by rw [hgx, e])
        obtain ⟨g', hg'⟩ := Option.ne_none_iff_exists'.1 hz
        show Real.toNNReal (tapeLo (pgM k) δ x zt (t + 1) (zt t)) ≤ _
        rw [hg']
        exact Real.toNNReal_le_toNNReal (tapeLo_grid hx _ _ _ _ _)
      · rw [ho1 g hg hgx]
        exact ih3 g hg hne
    · by_cases hgx : g = gid (vT (zt t))
      · rw [hgx, hy2 (children_term _)]
        show Real.toNNReal (tapeHi (pgM k) δ x zt (t + 1) (zt t)) ≤ 1
        exact (Real.toNNReal_le_toNNReal (tapeHi_le_one _ _ _ _ _ _)).trans_eq Real.toNNReal_one
      · rw [ho2 g hg hgx]
        exact ih4 g hg

/-! ### Root query -/

/-- Stored lower endpoint of a root action. -/
def pgL (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (a : Fin (pgD k + 1)) : ℝ := ((pgState δ x zt t).1.val (gid (pgGate k a)) : ℝ)

/-- Stored upper endpoint of a root action. -/
def pgU (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (a : Fin (pgD k + 1)) : ℝ := ((pgState δ x zt t).2.val (gid (pgGate k a)) : ℝ)

/-- The stopping test of the root query after `t` rollouts, at `ε = 1/5`: `a` is the
canonical lower-bound leader and every rival has `U - L(a) ≤ 1/5`. -/
def pgStops (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (a : Fin (pgD k + 1)) : Prop :=
  MarginalStops univ (pgL δ x zt t) (pgU δ x zt t) (1 / 5) a

lemma pgU_le_one (hx : PGTape x) (δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (a : Fin (pgD k + 1)) : pgU δ x zt t a ≤ 1 := by
  have h := inv_val_le pgDag_wf (pgState_inv δ x zt t).2 (fun _ => True) (fun _ _ _ _ => trivial)
    1 (fun g _ hg => (pgState_leaves hx δ zt t).2.2.2 g hg) (gid (pgGate k a)) trivial
  exact (NNReal.coe_le_coe.2 h).trans_eq NNReal.coe_one

lemma pgL_lose (hx : PGTape x) (δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) (i : Fin (pgD k)) :
    pgL δ x zt t i.castSucc ≤ 0.03 := by
  have h := inv_val_le pgDag_wf (pgState_inv δ x zt t).1
    (fun g => ∃ v : PV k, g = gid v ∧ v ≠ vT none ∧ v ≠ vR)
    (by
      rintro g ⟨v, rfl, hv1, hv2⟩ c hc
      obtain ⟨w, v', e, rfl, he⟩ := mem_children.1 hc
      have e' : v = w := gid_injective e
      subst e'
      refine ⟨v', rfl, ?_, ?_⟩
      · intro e'
        rw [e'] at he
        rcases he.of_child_term with ⟨cc, y, -, hy, -⟩ | ⟨hr, -⟩
        · simp at hy
        · exact hv2 hr
      · intro e'
        rw [e'] at he
        exact he.not_child_root)
    (Real.toNNReal 0.03)
    (by
      rintro g ⟨v, rfl, hv1, -⟩ hg
      exact (pgState_leaves hx δ zt t).2.2.1 _ hg (fun e => hv1 (gid_injective e)))
    (gid (pgGate k i.castSucc)) ⟨_, rfl, by simp, by simp⟩
  have h' := NNReal.coe_le_coe.2 h
  rw [Real.coe_toNNReal 0.03 (by norm_num)] at h'
  exact h'

lemma pgL_win (hx : PGTape x) (δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    tapeLo (pgM k) δ x zt t none ≤ pgL δ x zt t (Fin.last _) := by
  unfold pgL
  rw [pgGate_last, (pgState_leaves hx δ zt t).1 none]
  exact Real.le_coe_toNNReal _

lemma pgU_win (hx : PGTape x) (δ : ℝ) (zt : ℕ → GridTerminal k) (t : ℕ) :
    tapeHi (pgM k) δ x zt t none ≤ pgU δ x zt t (Fin.last _) := by
  unfold pgU
  rw [pgGate_last, (pgState_leaves hx δ zt t).2.1 none]
  exact Real.le_coe_toNNReal _

/-- **Any successful stopping test recommends `w*`.** -/
theorem pgStops_leader (hx : PGTape x) {δ : ℝ} {zt : ℕ → GridTerminal k} {t : ℕ}
    {a : Fin (pgD k + 1)} (hs : pgStops δ x zt t a) : a = Fin.last _ := by
  by_contra ha
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
  · have h1 := hs.2 (Fin.last _) (mem_univ _) (Ne.symm ha)
    have h2 := pgL_lose hx δ zt t i
    have h3 := pgU_win hx δ zt t
    have h4 := tapeHi_win hx (pgM k) δ zt t
    linarith
  · exact ha rfl

/-- **The stopping test passes once the lower endpoint of `w*` is at least `4/5`.** -/
theorem pgStops_of_lower (hx : PGTape x) {δ : ℝ} {zt : ℕ → GridTerminal k} {t : ℕ}
    (h45 : 4 / 5 ≤ tapeLo (pgM k) δ x zt t none) : pgStops δ x zt t (Fin.last _) := by
  have hw := pgL_win hx δ zt t
  refine ⟨⟨mem_univ _, fun b _ => ?_, fun b _ hbe => ?_⟩, fun b _ hne => ?_⟩
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨i, rfl⟩ | rfl
    · have := pgL_lose hx δ zt t i
      linarith
    · exact le_rfl
  · rcases Fin.eq_castSucc_or_eq_last b with ⟨i, rfl⟩ | rfl
    · have := pgL_lose hx δ zt t i
      linarith
    · exact le_rfl
  · have := pgU_le_one hx δ zt t b
    linarith

/-! ### Stopping time -/

/-- A count from which the Hoeffding radius is below `0.18`. -/
def pgK0 (k : ℕ) (δ : ℝ) : ℕ :=
  ⌈32 / (9 / 25 : ℝ) ^ 2 * Real.log (32 * pgM k / (δ * (9 / 25) ^ 2))⌉₊

lemma pgM_ge : (2 : ℝ) ≤ pgM k := by
  unfold pgM
  have h1 := one_le_r (k := k)
  have h2 : 2 ≤ 2 ^ k * 2 ^ k + 1 := by nlinarith
  exact_mod_cast h2

lemma pgWidth_lt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {n : ℕ} (hn : pgK0 k δ ≤ n) :
    hoeffdingWidth (pgM k) δ n < 9 / 25 :=
  width_inversion pgM_ge hδ0 hδ1 (by norm_num) (by norm_num)
    ((Nat.le_ceil _).trans (by exact_mod_cast hn))

variable {sel : ℕ → Fin (pgD k + 1)} {zt : ℕ → GridTerminal k}

/-- **Stopping** (the hypothesis `hstop` of `CostEngines.parity_total_work`, derived).  If
`T ≥ d + 1` and `T ≥ k₀ + d (1 + 5 log (1 + T))`, then after `T` rollouts the root query
stops and recommends `w*`. -/
theorem parity_stops_by (h : ParitySearch x sel zt) (hx : PGTape x) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {T : ℕ} (hT : pgD k + 1 ≤ T)
    (hTk : (pgK0 k δ : ℝ) + pgD k * (1 + 5 * Real.log (1 + T)) ≤ T) :
    pgStops δ x zt T (Fin.last _) := by
  apply pgStops_of_lower hx
  have hcnt := h.win_count_ge hx hT
  have hq : queryCount zt T none = uctCount sel T (Fin.last _) := by
    unfold queryCount uctCount
    congr 1
    exact Finset.filter_congr (fun s _ => h.zt_none_iff s)
  have hk : pgK0 k δ ≤ queryCount zt T none := by
    rw [hq]
    have : (pgK0 k δ : ℝ) ≤ uctCount sel T (Fin.last (pgD k)) := by linarith
    exact_mod_cast this
  have hpos : queryCount zt T none ≠ 0 := by
    rw [hq]
    have := h.uct.one_le (Fin.last _) (t := T) (by rw [Fintype.card_fin]; exact hT)
    omega
  have h1 := tapeLo_win hx (pgM k) δ zt T hpos
  have h2 := pgWidth_lt hδ0 hδ1 hk
  linarith

end Monitor

/-! ## Step 3c: total work -/

section Work

variable {k : ℕ}

/-- The coordinate of a terminal in the orientation `f`. -/
def pgCoord (f : Bool) : GridTerminal k → Mask k
  | none => 0
  | some x => if f then x.1 else x.2

/-- Allocator work of one rollout through root action `a` reaching terminal `z`: one index
evaluation per child of every node on the path (the root; for a parity action also the
action gate and the coordinate gate of `z`), plus `9` units for the at most three steps
down and back up, the root statistics and the terminal table update. -/
def pgRolloutCost (a : Fin (pgD k + 1)) (z : GridTerminal k) : ℕ :=
  (cV k (vR : PV k)).card
    + Fin.lastCases (motive := fun _ => ℕ) 0
        (fun i => (cV k (vA i)).card
          + (cV k (vC ((pgIdx k i).1, pgCoord (pgIdx k i).1 z))).card) a + 9

lemma pgRolloutCost_le (a : Fin (pgD k + 1)) (z : GridTerminal k) :
    pgRolloutCost a z ≤ 7 * 2 ^ k + 6 := by
  have h1 := cV_root_card_le (k := k)
  have hd := pgD_le (k := k)
  unfold pgRolloutCost
  rcases Fin.eq_castSucc_or_eq_last a with ⟨i, rfl⟩ | rfl
  · rw [Fin.lastCases_castSucc]
    have h2 := cV_act_card_le i
    have h3 := cV_coord_card (k := k) ((pgIdx k i).1, pgCoord (pgIdx k i).1 z)
    omega
  · rw [Fin.lastCases_last]
    omega

/-- Initialisation: writing the stored value of every vertex and the heap key of every
incidence, for both endpoints. -/
def pgInitCost (k : ℕ) : ℕ := 2 * ((pgDag k).N + pgE k)

/-- Root query: two scans of the `d + 1` root actions. -/
def pgQueryCost (k : ℕ) : ℕ := 2 * (pgD k + 1)

/-- **Total work of `T` rollouts with direct graph maintenance**: initialisation, the
allocator work of every rollout, the interval wave of the engine after every rollout (its
cost is computed by the engine), and a root query at each of the times `0, …, T`. -/
def pgWork (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (T : ℕ) : ℕ :=
  pgInitCost k + ∑ s ∈ range T, pgRolloutCost (sel s) (zt s)
    + ∑ t ∈ Icc 1 T, waveCost (pgDag k) (pgUpd δ x zt) (pgInit k) t
    + (T + 1) * pgQueryCost k

/-- **Work of one interval wave on the parity grid**: at most `2 (6 + (k + 5)(4r + 2))`,
that is `O(r log r)` (`CostEngines.ivWave_cost_three_layers` with the shape bounds
`pgDag_shape` and degree bound `pgDag_degree`). -/
theorem pgWave_le (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (zt : ℕ → GridTerminal k) (t : ℕ)
    (ht : 1 ≤ t) :
    waveCost (pgDag k) (pgUpd δ x zt) (pgInit k) t ≤ 2 * (6 + (k + 5) * (4 * 2 ^ k + 2)) := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hinv := pgState_inv δ x zt t
  obtain ⟨s0, s1, s2, s3⟩ := pgDag_shape (zt t)
  have hc : Nat.clog 2 (4 * 2 ^ k) ≤ k + 2 :=
    Nat.clog_le_of_le_pow (by rw [pow_succ, pow_succ]; omega)
  have h := ivWave_cost_three_layers pgDag_wf (gid (vT (zt t)))
    (pgTab δ x zt (t + 1) (zt t)).1 (pgTab δ x zt (t + 1) (zt t)).2 (pgState δ x zt t)
    (gid_lt _) hinv (4 * 2 ^ k) 2 (2 ^ k) 1 pgDag_degree s0 s1 s2 s3
  rw [waveCost_succ, pgUpd_succ]
  refine h.trans ?_
  have hL : (pgDag k).L = 3 := rfl
  rw [hL]
  have h4 : 2 + 2 * 2 ^ k + 2 * 2 ^ k * 1 = 4 * 2 ^ k + 2 := by ring
  rw [h4]
  have h5 : (Nat.clog 2 (4 * 2 ^ k) + 3) * (4 * 2 ^ k + 2) ≤ (k + 5) * (4 * 2 ^ k + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

/-- **Total work, in natural numbers**:
`W(T) ≤ 36 r² + 8 r + T (15 r + 18 + 2 (k + 5)(4 r + 2))`. -/
theorem pgWork_le (δ : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) (T : ℕ) :
    pgWork δ x sel zt T ≤ 36 * (2 ^ k * 2 ^ k) + 8 * 2 ^ k
      + T * (15 * 2 ^ k + 18 + 2 * ((k + 5) * (4 * 2 ^ k + 2))) := by
  obtain ⟨-, hN, -, hE⟩ := pgDag_size (k := k)
  have hd := pgD_le (k := k)
  have h1 : ∑ s ∈ range T, pgRolloutCost (sel s) (zt s) ≤ T * (7 * 2 ^ k + 6) := by
    have := Finset.sum_le_card_nsmul (range T) (fun s => pgRolloutCost (sel s) (zt s))
      (7 * 2 ^ k + 6) (fun s _ => pgRolloutCost_le _ _)
    rwa [card_range, smul_eq_mul] at this
  have h2 : ∑ t ∈ Icc 1 T, waveCost (pgDag k) (pgUpd δ x zt) (pgInit k) t
      ≤ T * (2 * (6 + (k + 5) * (4 * 2 ^ k + 2))) := by
    have := Finset.sum_le_card_nsmul (Icc 1 T)
      (fun t => waveCost (pgDag k) (pgUpd δ x zt) (pgInit k) t)
      (2 * (6 + (k + 5) * (4 * 2 ^ k + 2))) (fun t ht => pgWave_le δ x zt t (mem_Icc.1 ht).1)
    rwa [Nat.card_Icc, smul_eq_mul, Nat.add_sub_cancel] at this
  have h3 : (T + 1) * pgQueryCost k ≤ (T + 1) * (8 * 2 ^ k) :=
    Nat.mul_le_mul_left _ (by unfold pgQueryCost; omega)
  unfold pgWork pgInitCost
  generalize 2 ^ k = r at *
  generalize (k + 5) * (4 * r + 2) = Y at *
  nlinarith

end Work

/-! ## Assembly: `thm:coded-main` / `thm:coded-covers` -/

section Final

variable {k : ℕ}

/-- **`τ = O(r log r)`.**  There is a constant `A` depending only on `δ` such that for every
`k ≥ 2` some `T ≤ A r log r` satisfies the hypothesis of `parity_stops_by`. -/
theorem pg_horizon_exists {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A : ℝ, 0 < A ∧ ∀ k : ℕ, 2 ≤ k → ∃ T : ℕ, pgD k + 1 ≤ T ∧
      (T : ℝ) ≤ A * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) ∧
      (pgK0 k δ : ℝ) + pgD k * (1 + 5 * Real.log (1 + T)) ≤ T := by
  obtain ⟨A, hA, hhor⟩ := core_horizon_exists hδ0 hδ1
  refine ⟨200 * A, by positivity, ?_⟩
  intro k hk
  obtain ⟨r, hr⟩ : ∃ r : ℕ, r = 2 ^ k := ⟨_, rfl⟩
  have hr4 : 4 ≤ r := by
    rw [hr]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨T, hT1, hT2, hT3⟩ := hhor (20 * r) (by omega)
  have hd := pgD_le (k := k)
  rw [← hr] at hd
  have hrR : (4 : ℝ) ≤ r := by exact_mod_cast hr4
  have hrpow : ((2 : ℝ) ^ k) = r := by
    rw [hr]
    push_cast
    rfl
  have hM : pgM k = (r : ℝ) ^ 2 + 1 := by
    unfold pgM
    rw [← hr]
    push_cast
    ring
  rw [hrpow]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log r := ⟨_, rfl⟩
  rw [← hℓ]
  have hℓ1 : 1 ≤ ℓ := by
    have h4 : 1 ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    rw [hℓ]
    exact h4.trans (Real.log_le_log (by norm_num) hrR)
  have hr0 : (0 : ℝ) < r := by linarith
  push_cast at hT2 hT3
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  obtain ⟨Lt, hLt⟩ : ∃ Lt : ℝ, Lt = Real.log (1 + (T : ℝ)) := ⟨_, rfl⟩
  rw [← hLt] at hT3
  have hLt0 : 0 ≤ Lt := by
    rw [hLt]
    exact Real.log_nonneg (by linarith)
  have hl2 := Real.log_two_lt_d9
  refine ⟨2 * T, by omega, ?_, ?_⟩
  · -- the horizon is `O(r log r)`
    have hlog20 : Real.log (20 * (r : ℝ)) ≤ 5 * ℓ := by
      rw [Real.log_mul (by norm_num) hr0.ne', ← hℓ]
      have h20 : Real.log 20 ≤ Real.log (2 ^ 5) := Real.log_le_log (by norm_num) (by norm_num)
      rw [Real.log_pow] at h20
      push_cast at h20
      linarith
    have h1 : A * (20 * (r : ℝ)) * Real.log (20 * (r : ℝ)) ≤ A * (20 * (r : ℝ)) * (5 * ℓ) :=
      mul_le_mul_of_nonneg_left hlog20 (by positivity)
    push_cast
    nlinarith
  · -- the count threshold is reached
    have hlog2T : Real.log (1 + ((2 * T : ℕ) : ℝ)) ≤ 1 + Lt := by
      push_cast
      have h1 : Real.log (1 + 2 * (T : ℝ)) ≤ Real.log (2 * (1 + (T : ℝ))) :=
        Real.log_le_log (by linarith) (by linarith)
      have h2 : Real.log (2 * (1 + (T : ℝ))) = Real.log 2 + Lt := by
        rw [hLt]
        exact Real.log_mul (by norm_num) (by linarith)
      linarith
    have hl2T0 : 0 ≤ Real.log (1 + ((2 * T : ℕ) : ℝ)) :=
      Real.log_nonneg (by
        have : (0 : ℝ) ≤ ((2 * T : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith)
    obtain ⟨M', hM'⟩ : ∃ M' : ℝ, M' = (((20 * r) ^ 2 + 20 * r + 1 : ℕ) : ℝ) := ⟨_, rfl⟩
    have hM'e : M' = 400 * (r : ℝ) ^ 2 + 20 * r + 1 := by
      rw [hM']
      push_cast
      ring
    have hMpos : 0 < pgM k := by
      rw [hM]
      positivity
    have hM'pos : 1 ≤ M' := by
      rw [hM'e]
      nlinarith
    obtain ⟨Lc, hLc⟩ : ∃ Lc : ℝ, Lc = Real.log (200 * M' / δ) := ⟨_, rfl⟩
    have harg : 32 * pgM k / (δ * (9 / 25) ^ 2) ≤ 200 * M' / δ := by
      rw [div_le_div_iff₀ (by positivity) hδ0, hM, hM'e]
      have hr2 : 0 ≤ (r : ℝ) ^ 2 := by positivity
      nlinarith [mul_nonneg hr2 hδ0.le, mul_nonneg hr0.le hδ0.le]
    have harg1 : 1 ≤ 32 * pgM k / (δ * (9 / 25) ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have := pgM_ge (k := k)
      nlinarith
    have hLc1 : 1 ≤ Lc := by
      rw [hLc, Real.le_log_iff_exp_le (by positivity)]
      have h1 := Real.exp_one_lt_d9
      have h2 : (200 : ℝ) ≤ 200 * M' / δ := by
        rw [le_div_iff₀ hδ0]
        nlinarith
      linarith
    have hlog0 : 0 ≤ Real.log (32 * pgM k / (δ * (9 / 25) ^ 2)) := Real.log_nonneg harg1
    have hlogle : Real.log (32 * pgM k / (δ * (9 / 25) ^ 2)) ≤ Lc := by
      rw [hLc]
      exact Real.log_le_log (by linarith) harg
    have hK0 : (pgK0 k δ : ℝ) ≤ 248 * Lc := by
      have hc : (32 : ℝ) / (9 / 25) ^ 2 ≤ 247 := by norm_num
      have hx0 : 0 ≤ 32 / (9 / 25 : ℝ) ^ 2 * Real.log (32 * pgM k / (δ * (9 / 25) ^ 2)) :=
        mul_nonneg (by norm_num) hlog0
      have h1 : (pgK0 k δ : ℝ)
          < 32 / (9 / 25 : ℝ) ^ 2 * Real.log (32 * pgM k / (δ * (9 / 25) ^ 2)) + 1 :=
        Nat.ceil_lt_add_one hx0
      have h2 : 32 / (9 / 25 : ℝ) ^ 2 * Real.log (32 * pgM k / (δ * (9 / 25) ^ 2))
          ≤ 247 * Lc := mul_le_mul hc hlogle hlog0 (by norm_num)
      linarith
    have hcK : 200 * Lc ≤ (coreK0 (20 * r) δ : ℝ) := by
      rw [hLc, hM']
      exact Nat.le_ceil _
    have hdR : (pgD k : ℝ) ≤ 4 * r := by
      have : pgD k ≤ 4 * r := by omega
      exact_mod_cast this
    have hd1 : (pgD k : ℝ) * (1 + 5 * Real.log (1 + ((2 * T : ℕ) : ℝ)))
        ≤ 4 * r * (6 + 5 * Lt) :=
      mul_le_mul hdR (by linarith) (by linarith) (by positivity)
    have hrL : 0 ≤ (r : ℝ) * Lt := mul_nonneg hr0.le hLt0
    have e2T : (((2 * T : ℕ) : ℕ) : ℝ) = 2 * (T : ℝ) := by push_cast; ring
    rw [e2T] at hd1 ⊢
    nlinarith

/-- The pathwise conclusion of the upper half of `thm:coded-covers` for a search
`(sel, zt)` on the tapes `x`: the first rollout count `τ` at which the root query stops
exists, the query recommends `w*` there, any successful query recommends `w*`,
`τ ≤ A r log r`, and the total work up to `τ` is at most `B r² log² r`. -/
def PGCertified (δ A B : ℝ) (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1))
    (zt : ℕ → GridTerminal k) : Prop :=
  ∃ τ : ℕ, pgStops δ x zt τ (Fin.last _) ∧
    (∀ t, t < τ → ∀ a, ¬ pgStops δ x zt t a) ∧
    (∀ t a, pgStops δ x zt t a → a = Fin.last _) ∧
    (τ : ℝ) ≤ A * (2 : ℝ) ^ k * Real.log ((2 : ℝ) ^ k) ∧
    (pgWork δ x sel zt τ : ℝ) ≤ B * ((2 : ℝ) ^ k) ^ 2 * Real.log ((2 : ℝ) ^ k) ^ 2

/-- **Step 3 of `thm:coded-covers`, pathwise.**  Fix `δ ∈ (0, 1)`.  There are constants
`A, B` such that for every `k ≥ 2`, every reward tape with the stated ranges and every UCT
search on the parity-grid DAG, direct graph maintenance stops within `A r log r` rollouts,
recommends `w*`, and has done at most `B r² log² r` work.  No probabilistic input is used:
the reward ranges alone force stopping. -/
theorem parity_certified {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ (x : GridTerminal k → ℕ → ℝ) (sel : ℕ → Fin (pgD k + 1)) (zt : ℕ → GridTerminal k),
      PGTape x → ParitySearch x sel zt → PGCertified δ A B x sel zt := by
  classical
  obtain ⟨A, hA, hhor⟩ := pg_horizon_exists hδ0 hδ1
  refine ⟨A, 90 * A + 38, hA, by linarith, ?_⟩
  intro k hk x sel zt hx h
  obtain ⟨T, hT1, hT2, hT3⟩ := hhor k hk
  have hstopT := parity_stops_by h hx hδ0 hδ1 hT1 hT3
  have hlead : ∀ t a, pgStops δ x zt t a → a = Fin.last _ := fun t a hs => pgStops_leader hx hs
  have hex : ∃ t, ∃ a, pgStops δ x zt t a := ⟨T, _, hstopT⟩
  obtain ⟨a, ha⟩ := Nat.find_spec hex
  have hτT : Nat.find hex ≤ T := Nat.find_min' hex ⟨_, hstopT⟩
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = Nat.find hex := ⟨_, rfl⟩
  rw [← hτ] at ha hτT
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
  rw [← hr, ← hℓ] at hT2
  have hτR : (τ : ℝ) ≤ A * r * ℓ := le_trans (by exact_mod_cast hτT) hT2
  refine ⟨τ, ?_, ?_, hlead, ?_, ?_⟩
  · rw [hlead τ a ha] at ha
    exact ha
  · intro t ht a' hs
    rw [hτ] at ht
    exact Nat.find_min hex ht ⟨a', hs⟩
  · rw [← hr, ← hℓ]
    exact hτR
  · rw [← hr, ← hℓ]
    have hW := pgWork_le δ x sel zt τ
    have hWR : (pgWork δ x sel zt τ : ℝ) ≤ 36 * (r * r) + 8 * r
        + τ * (15 * r + 18 + 2 * (((k : ℝ) + 5) * (4 * r + 2))) := by
      rw [hr]
      exact_mod_cast hW
    have hτ0 : (0 : ℝ) ≤ τ := Nat.cast_nonneg τ
    have hk5 : (k : ℝ) + 5 ≤ 7 * ℓ := by linarith
    have h42 : 4 * r + 2 ≤ 5 * r := by linarith
    have hp : ((k : ℝ) + 5) * (4 * r + 2) ≤ 7 * ℓ * (5 * r) :=
      mul_le_mul hk5 h42 (by linarith) (by linarith)
    have hrℓ : r ≤ r * ℓ := le_mul_of_one_le_right (by linarith) hℓ1
    have hper : 15 * r + 18 + 2 * (((k : ℝ) + 5) * (4 * r + 2)) ≤ 90 * (r * ℓ) := by
      nlinarith
    have hper0 : (0 : ℝ) ≤ 15 * r + 18 + 2 * (((k : ℝ) + 5) * (4 * r + 2)) := by
      have : (0 : ℝ) ≤ ((k : ℝ) + 5) * (4 * r + 2) := by positivity
      linarith
    have h1 : (τ : ℝ) * (15 * r + 18 + 2 * (((k : ℝ) + 5) * (4 * r + 2)))
        ≤ A * r * ℓ * (90 * (r * ℓ)) :=
      mul_le_mul hτR hper hper0 (by positivity)
    have hr2 : 16 ≤ r ^ 2 := by nlinarith
    have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
    have h2 : 36 * (r * r) + 8 * r ≤ 38 * (r ^ 2 * ℓ ^ 2) := by
      have hb : 8 * r ≤ 2 * r ^ 2 := by nlinarith
      have hc : r ^ 2 ≤ r ^ 2 * ℓ ^ 2 := le_mul_of_one_le_right (by positivity) hℓ2
      nlinarith
    have e : (90 * A + 38) * r ^ 2 * ℓ ^ 2 = A * r * ℓ * (90 * (r * ℓ)) + 38 * (r ^ 2 * ℓ ^ 2) := by
      ring
    linarith

/-- **Theorems `thm:coded-main` and `thm:coded-covers`.**  Fix `δ ∈ (0, 1)`.  There are
constants `A, B` (depending only on `δ`) such that for every `k ≥ 2`, with `r = 2^k`:

1. the parity-grid DAG `pgDag k` has `r² ≤ |V| ≤ 7r²` vertices and `2r² ≤ |E| ≤ 11r²`
   edges, its `d + 1 = 4(r - 1) + 1` root supports are pairwise distinct, and `w*` is the
   unique `1/5`-optimal root action for the means `0.99` (`w*`) and `0.02` (grid);
2. (every layout) for every terminal ordering `π` and every family of dyadic covers of the
   parity root supports under `π`, the covers contain at least `r³ / 2` blocks in total;
3. (direct graph maintenance) for every probability space carrying reward tapes that are
   independent within each tape, have the stated ranges almost surely and the stated means,
   and for every UCT search (`c = 2`, any tie-breaking, any selections below the root) run
   on these tapes: outside an event of probability at most `δ`, the true means lie in the
   Hoeffding box at every time, the root query stops within `A r log r` rollouts and
   recommends `w*` (and never anything else), and the total work up to the stopping time is
   at most `B r² log² r`.

In 3 only the coverage statement uses probability; stopping and the work bound hold almost
surely.  "Direct graph maintenance" is the eager interval engine of `CostEngines.lean`; the
retiring ("Graph Selective") monitor is not modelled.  In 2 the count is of root-to-block
incidences, a lower bound on the work of any compiler that writes them. -/
theorem coded_main {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
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
            PGCertified δ A B (fun z i => X z i ω) (sel ω) (zt ω))} ≤ ENNReal.ofReal δ) := by
  obtain ⟨A, B, hA, hB, hpath⟩ := parity_certified hδ0 hδ1
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
          PGCertified δ A B (fun z i => X z i ω) (sel ω) (zt ω))}
        ⊆ {ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          ∪ {ω | ¬ PGTape (fun z i => X z i ω)} := by
      intro ω hω
      by_cases hx : PGTape (fun z i => X z i ω)
      · left
        intro hc
        exact hω ⟨hc, hpath k hk _ _ _ hx (hsearch ω)⟩
      · right
        exact hx
    calc P {ω | ¬ (tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k) ∧
            PGCertified δ A B (fun z i => X z i ω) (sel ω) (zt ω))}
        ≤ P ({ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          ∪ {ω | ¬ PGTape (fun z i => X z i ω)}) := measure_mono hsub
      _ ≤ P {ω | ¬ tapeCovered (pgM k) δ (fun z i => X z i ω) (zt ω) (pgMean k)}
          + P {ω | ¬ PGTape (fun z i => X z i ω)} := measure_union_le _ _
      _ ≤ ENNReal.ofReal δ := by
          rw [hnull, add_zero]
          exact hcov

end Final

end

end ParityGrid
end JointRootCert
