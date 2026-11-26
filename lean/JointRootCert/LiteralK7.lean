/-
Joint Root Certification: `thm:adaptive-oracle-coupling` / `thm:charged-dual-cover` (Exact
coupling and charged maintenance), with one shared segment tree, a global min-heap on the
certificate, charged bookkeeping, linear-time initialisation and a memory-model footprint.

IMPORTS `JointRootCert.LiteralK7a` (bottom-up heap construction).

Manuscript result covered:

* `thm:charged-dual-cover`, all quantitative clauses, and the oracle part of
  `thm:adaptive-oracle-coupling`.

## The index (`IState`)
ONE shared segment-tree array whose node `(k, j)` holds the pair (max of lower values, max of
upper values) over its dyadic block; per root action an indexed max-heap on the lower maxima
of the blocks of `C_a⁺` and one on the upper maxima of the blocks of `C_a⁻`; ONE global
indexed heap over the root actions with key `gk U⁻(a) L(a) a`; a mark array.  All heap
operations are executed by `HeapImpl`.

* `iUpdate` / `iUpdate_spec`: one terminal update, with the change detection, the
  construction of the changed-subscription lists `𝒩_t^±` (`subsList`), the deliveries, the
  construction of the affected-action list `𝒜_t` with marks (`collect`), the global-heap
  refresh and the clearing of the marks all charged; cost `≤ updCost`
  `= 7 (h + Σ_{𝒩_t⁺} ⌈log₂(2+b_a⁺)⌉ + Σ_{𝒩_t⁻} ⌈log₂(2+b_a⁻)⌉ + |𝒜_t| ⌈log₂(2+K)⌉)`.
* `iInit` / `iInit_spec`: tree build plus bottom-up heap construction (`LiteralK7a.build`),
  cost `≤ (2^(n+1) - 1) + Σ_a (8 b_a⁺ + 1) + Σ_a (8 b_a⁻ + 1) + 10 K` (linear: the `M + B + K`
  terms).
* `iRun_spec`, `query_reply`: runs of updates and queries; each query is one read of the
  global-heap root and returns the specification reply `boxReply`.
* `minKey`, `boxReply_minimiser`: with keys in `RKey` (order dual of lexicographic
  (value, action)), the global max-heap is a min-heap on `R_t(a) = φ(U_t⁻(a)) - φ(L_t(a))`
  and the query returns a minimiser (ties: smallest action identifier).
* `dualImpl`, `dual_answer_eq`, `dual_cover_oracle`: the index is an
  `Representation.OracleImpl` whose answer equals, on every history, the specification
  oracle computed from the terminal box; `Representation.exact_coupling` then gives identical
  histories, replies and stopping times (first sentence of the theorem).
* `PG_le`: the computed run-merging cost (`RunMerge.gateCost`, pairwise merging) is at most
  `3 Σ_v pgTerm v`, the right-hand side of `eq:dual-run-compilation`; the needed
  `|E(v)| ≤ A_v` is derived from the support equations (`supp_nonempty`).
* `heapCells`, `iFootprint`, `iFootprint_le`, `TreeFits`: memory model.  A heap occupies its
  handle and key arrays of length `n` plus one cell per entry of its handle-to-position map;
  the tree occupies `2 |nodeSet n|` cells and is proved to be blank outside them.
* `charged_dual_cover_literal`: the assembled statement (covers, `B ≤ 2h(2R_run+K)`,
  replies, total work in the form of `eq:dual-cover-work`, `P_G`, footprint
  `≤ |V| + 2|E| + 8M + 5B + 4K`).

## Differences from the manuscript
* Run merging is pairwise (`RunMerge.mergeAll`), not by a min-heap; its cost is within a
  factor 3 of `eq:dual-run-compilation`.
* Ties in the minimiser query are broken by the action identifier, not by `(u_t(z), -z)`.
* Heap slots at positions `≥ n` are treated as unallocated (their contents do not enter any
  representation statement); the peak space of the compile phase (temporary run lists) is not
  part of the footprint bound.
* A query costs one unit (one read).  Unit charges by definition: one per array write, per
  scanned list node, per mark write.
-/
import JointRootCert.DualCoverFinal
import JointRootCert.LiteralK7a

namespace JointRootCert
namespace LiteralK7

open Finset CostModel CostEngines RunMerge DualCoverFinal
open _root_.JointRootCert.Representation
open HeapImpl (Heap Rep findMax updateKey deliverH deliverH_spec)

/-! ## Costed list bookkeeping -/

section Book

variable {X Y A : Type*}

/-- Costed map: emit `f x` for every `x`, `c` units each. -/
def cmap (f : X → Y) (c : ℕ) : List X → List Y × ℕ
  | [] => ([], 0)
  | x :: xs => (f x :: (cmap f c xs).1, (cmap f c xs).2 + c)

lemma cmap_spec (f : X → Y) (c : ℕ) : ∀ xs : List X,
    (cmap f c xs).1 = xs.map f ∧ (cmap f c xs).2 = xs.length * c := by
  intro xs
  induction xs with
  | nil => exact ⟨rfl, by simp [cmap]⟩
  | cons x xs ih =>
    refine ⟨?_, ?_⟩
    · show f x :: (cmap f c xs).1 = _
      rw [ih.1, List.map_cons]
    · show (cmap f c xs).2 + c = _
      rw [ih.2, List.length_cons]
      ring

/-- **Construction of the changed-subscription list** `𝒩_t`: for every changed block read
its reverse-subscription list and emit one pair per subscribed action.  One unit per
changed block and one per emitted pair. -/
def subsList (subs : ℕ × ℕ → List A) : List (ℕ × ℕ) → List ((ℕ × ℕ) × A) × ℕ
  | [] => ([], 0)
  | d :: ds =>
    ((cmap (fun a => (d, a)) 1 (subs d)).1 ++ (subsList subs ds).1,
     (cmap (fun a => (d, a)) 1 (subs d)).2 + 1 + (subsList subs ds).2)

lemma subsList_spec (subs : ℕ × ℕ → List A) : ∀ ds : List (ℕ × ℕ),
    (subsList subs ds).1 = ds.flatMap (fun d => (subs d).map (fun a => (d, a))) ∧
    (subsList subs ds).2 = ds.length + (subsList subs ds).1.length := by
  intro ds
  induction ds with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    obtain ⟨c1, c2⟩ := cmap_spec (fun a => (d, a)) 1 (subs d)
    refine ⟨?_, ?_⟩
    · show (cmap (fun a => (d, a)) 1 (subs d)).1 ++ (subsList subs ds).1 = _
      rw [c1, ih.1, List.flatMap_cons]
    · show (cmap (fun a => (d, a)) 1 (subs d)).2 + 1 + (subsList subs ds).2
        = (ds.length + 1) + ((cmap (fun a => (d, a)) 1 (subs d)).1 ++ (subsList subs ds).1).length
      rw [c2, ih.2, List.length_append, c1, List.length_map]
      omega

variable [DecidableEq A]

/-- **Construction of the affected-action list** `𝒜_t` with a mark array: scan the changed
subscriptions; an action not yet marked is marked and appended.  One unit per scanned
subscription. -/
def collect : List ((ℕ × ℕ) × A) → (A → Bool) → List A → ((A → Bool) × List A) × ℕ
  | [], mrk, acc => ((mrk, acc), 0)
  | e :: es, mrk, acc =>
    if mrk e.2 = true then ((collect es mrk acc).1, (collect es mrk acc).2 + 1)
    else ((collect es (Function.update mrk e.2 true) (e.2 :: acc)).1,
          (collect es (Function.update mrk e.2 true) (e.2 :: acc)).2 + 1)

theorem collect_spec : ∀ (es : List ((ℕ × ℕ) × A)) (mrk : A → Bool) (acc : List A),
    (∀ a, mrk a = true ↔ a ∈ acc) → acc.Nodup →
    (∀ a, (collect es mrk acc).1.1 a = true ↔ a ∈ (collect es mrk acc).1.2) ∧
    (collect es mrk acc).1.2.Nodup ∧
    (∀ a, a ∈ (collect es mrk acc).1.2 ↔ a ∈ acc ∨ a ∈ es.map Prod.snd) ∧
    (collect es mrk acc).2 = es.length := by
  intro es
  induction es with
  | nil => intro mrk acc h1 h2; exact ⟨h1, h2, fun a => by simp [collect], rfl⟩
  | cons e es ih =>
    intro mrk acc h1 h2
    by_cases hm : mrk e.2 = true
    · have e0 : collect (e :: es) mrk acc = ((collect es mrk acc).1, (collect es mrk acc).2 + 1) := by
        rw [collect, ite_eq_left hm]
      rw [e0]
      obtain ⟨i1, i2, i3, i4⟩ := ih mrk acc h1 h2
      refine ⟨i1, i2, fun a => ?_, by show _ + 1 = _; rw [i4, List.length_cons]⟩
      show a ∈ (collect es mrk acc).1.2 ↔ _
      rw [i3 a, List.map_cons, List.mem_cons]
      have hacc := (h1 e.2).1 hm
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hacc)
        · exact Or.inr h
    · have e0 : collect (e :: es) mrk acc
          = ((collect es (Function.update mrk e.2 true) (e.2 :: acc)).1,
             (collect es (Function.update mrk e.2 true) (e.2 :: acc)).2 + 1) := by
        rw [collect, ite_eq_right hm]
      rw [e0]
      have h1' : ∀ a, Function.update mrk e.2 true a = true ↔ a ∈ e.2 :: acc := by
        intro a
        by_cases ha : a = e.2
        · rw [ha, Function.update_self]; simp
        · rw [Function.update_of_ne ha, h1 a, List.mem_cons]
          exact ⟨Or.inr, fun h => h.resolve_left ha⟩
      have h2' : (e.2 :: acc).Nodup :=
        List.nodup_cons.2 ⟨fun h => hm ((h1 e.2).2 h), h2⟩
      obtain ⟨i1, i2, i3, i4⟩ := ih _ _ h1' h2'
      refine ⟨i1, i2, fun a => ?_, by show _ + 1 = _; rw [i4, List.length_cons]⟩
      show a ∈ (collect es _ (e.2 :: acc)).1.2 ↔ _
      rw [i3 a, List.map_cons, List.mem_cons, List.mem_cons]
      tauto

/-- **Clearing the marks** of the affected actions: one unit each. -/
def clearMarks : List A → (A → Bool) → (A → Bool) × ℕ
  | [], mrk => (mrk, 0)
  | a :: as, mrk =>
    ((clearMarks as (Function.update mrk a false)).1,
     (clearMarks as (Function.update mrk a false)).2 + 1)

lemma clearMarks_spec : ∀ (L : List A) (mrk : A → Bool),
    (∀ a, (clearMarks L mrk).1 a = if a ∈ L then false else mrk a) ∧
    (clearMarks L mrk).2 = L.length := by
  intro L
  induction L with
  | nil => intro mrk; exact ⟨fun a => by simp [clearMarks], rfl⟩
  | cons b L ih =>
    intro mrk
    obtain ⟨i1, i2⟩ := ih (Function.update mrk b false)
    refine ⟨fun a => ?_, by show _ + 1 = _; rw [i2, List.length_cons]⟩
    show (clearMarks L (Function.update mrk b false)).1 a = _
    rw [i1 a]
    simp only [List.mem_cons]
    by_cases h1 : a ∈ L
    · simp [h1]
    · by_cases h2 : a = b
      · rw [h2]; simp
      · simp [h1, h2]

end Book

/-! ## One shared segment tree for both endpoint families -/

section Shared

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Lower-endpoint field of the shared tree array. -/
def prj1 (v : ℕ → ℕ → α × α) : ℕ → ℕ → α := fun k j => (v k j).1

/-- Upper-endpoint field of the shared tree array. -/
def prj2 (v : ℕ → ℕ → α × α) : ℕ → ℕ → α := fun k j => (v k j).2

/-- **Leaf-to-root recomputation in the shared tree.**  Every node holds the pair (maximum
of the lower values, maximum of the upper values) over its block.  Write `(x, y)` at leaf
`p` and recompute both fields of the nodes `(k, p / 2^k)`, `k = 1, …, n`.  Two units per
node. -/
def pathUpdate2 (p : ℕ) (x y : α) (v : ℕ → ℕ → α × α) : ℕ → (ℕ → ℕ → α × α) × ℕ
  | 0 => (setNode v 0 (p / 2 ^ 0) (x, y), 2)
  | k + 1 =>
    (setNode (pathUpdate2 p x y v k).1 (k + 1) (p / 2 ^ (k + 1))
        (((pathUpdate2 p x y v k).1 k (2 * (p / 2 ^ (k + 1)))).1
            ⊔ ((pathUpdate2 p x y v k).1 k (2 * (p / 2 ^ (k + 1)) + 1)).1,
         ((pathUpdate2 p x y v k).1 k (2 * (p / 2 ^ (k + 1)))).2
            ⊔ ((pathUpdate2 p x y v k).1 k (2 * (p / 2 ^ (k + 1)) + 1)).2),
      (pathUpdate2 p x y v k).2 + 2)

omit [OrderBot α] in
/-- The two fields of the shared tree evolve as the one-endpoint trees of
`CostModel.pathUpdate`. -/
lemma pathUpdate2_prj (p : ℕ) (x y : α) (v : ℕ → ℕ → α × α) : ∀ n,
    prj1 (pathUpdate2 p x y v n).1 = (pathUpdate p x (prj1 v) n).1 ∧
    prj2 (pathUpdate2 p x y v n).1 = (pathUpdate p y (prj2 v) n).1 ∧
    (pathUpdate2 p x y v n).2 = 2 * (n + 1) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, rfl⟩
    · funext k j
      show (setNode v 0 (p / 2 ^ 0) (x, y) k j).1 = setNode (prj1 v) 0 (p / 2 ^ 0) x k j
      unfold setNode prj1
      split_ifs <;> rfl
    · funext k j
      show (setNode v 0 (p / 2 ^ 0) (x, y) k j).2 = setNode (prj2 v) 0 (p / 2 ^ 0) y k j
      unfold setNode prj2
      split_ifs <;> rfl
  | succ n ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · funext k j
      show (setNode (pathUpdate2 p x y v n).1 (n + 1) (p / 2 ^ (n + 1)) _ k j).1
        = setNode (pathUpdate p x (prj1 v) n).1 (n + 1) (p / 2 ^ (n + 1))
            ((pathUpdate p x (prj1 v) n).1 n (2 * (p / 2 ^ (n + 1)))
              ⊔ (pathUpdate p x (prj1 v) n).1 n (2 * (p / 2 ^ (n + 1)) + 1)) k j
      rw [← i1]
      unfold setNode prj1
      split_ifs <;> rfl
    · funext k j
      show (setNode (pathUpdate2 p x y v n).1 (n + 1) (p / 2 ^ (n + 1)) _ k j).2
        = setNode (pathUpdate p y (prj2 v) n).1 (n + 1) (p / 2 ^ (n + 1))
            ((pathUpdate p y (prj2 v) n).1 n (2 * (p / 2 ^ (n + 1)))
              ⊔ (pathUpdate p y (prj2 v) n).1 n (2 * (p / 2 ^ (n + 1)) + 1)) k j
      rw [← i2]
      unfold setNode prj2
      split_ifs <;> rfl
    · show (pathUpdate2 p x y v n).2 + 2 = _
      rw [i3]
      ring

/-- **Build of the shared tree**, bottom up: level `0` holds the pairs of leaf values, a
node of level `k + 1` the fieldwise maximum of its two children.  One unit per node. -/
def treeBuild2 (n : ℕ) (fl fu : ℕ → α) (v0 : ℕ → ℕ → α × α) : ℕ → (ℕ → ℕ → α × α) × ℕ
  | 0 => fillLevel v0 0 (fun j => (fl j, fu j)) (2 ^ n)
  | k + 1 =>
    ((fillLevel (treeBuild2 n fl fu v0 k).1 (k + 1)
        (fun j => (((treeBuild2 n fl fu v0 k).1 k (2 * j)).1
                      ⊔ ((treeBuild2 n fl fu v0 k).1 k (2 * j + 1)).1,
                   ((treeBuild2 n fl fu v0 k).1 k (2 * j)).2
                      ⊔ ((treeBuild2 n fl fu v0 k).1 k (2 * j + 1)).2))
        (2 ^ (n - (k + 1)))).1,
     (treeBuild2 n fl fu v0 k).2 + (fillLevel (treeBuild2 n fl fu v0 k).1 (k + 1)
        (fun j => (((treeBuild2 n fl fu v0 k).1 k (2 * j)).1
                      ⊔ ((treeBuild2 n fl fu v0 k).1 k (2 * j + 1)).1,
                   ((treeBuild2 n fl fu v0 k).1 k (2 * j)).2
                      ⊔ ((treeBuild2 n fl fu v0 k).1 k (2 * j + 1)).2))
        (2 ^ (n - (k + 1)))).2)

omit [OrderBot α] in
lemma treeBuild2_prj (n : ℕ) (fl fu : ℕ → α) (v0 : ℕ → ℕ → α × α) : ∀ K,
    prj1 (treeBuild2 n fl fu v0 K).1 = (treeBuild n fl (prj1 v0) K).1 ∧
    prj2 (treeBuild2 n fl fu v0 K).1 = (treeBuild n fu (prj2 v0) K).1 ∧
    (treeBuild2 n fl fu v0 K).2 = (treeBuild n fl (prj1 v0) K).2 := by
  intro K
  induction K with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · funext k j
      show ((fillLevel v0 0 (fun j => (fl j, fu j)) (2 ^ n)).1 k j).1
        = (fillLevel (prj1 v0) 0 fl (2 ^ n)).1 k j
      rw [(fillLevel_spec _ _ _ _).1, (fillLevel_spec _ _ _ _).1]
      unfold prj1
      split_ifs <;> rfl
    · funext k j
      show ((fillLevel v0 0 (fun j => (fl j, fu j)) (2 ^ n)).1 k j).2
        = (fillLevel (prj2 v0) 0 fu (2 ^ n)).1 k j
      rw [(fillLevel_spec _ _ _ _).1, (fillLevel_spec _ _ _ _).1]
      unfold prj2
      split_ifs <;> rfl
    · show (fillLevel v0 0 (fun j => (fl j, fu j)) (2 ^ n)).2
        = (fillLevel (prj1 v0) 0 fl (2 ^ n)).2
      rw [(fillLevel_spec _ _ _ _).2, (fillLevel_spec _ _ _ _).2]
  | succ K ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · funext k j
      show ((fillLevel (treeBuild2 n fl fu v0 K).1 (K + 1) _ (2 ^ (n - (K + 1)))).1 k j).1
        = (fillLevel (treeBuild n fl (prj1 v0) K).1 (K + 1)
            (fun j => (treeBuild n fl (prj1 v0) K).1 K (2 * j)
              ⊔ (treeBuild n fl (prj1 v0) K).1 K (2 * j + 1)) (2 ^ (n - (K + 1)))).1 k j
      rw [(fillLevel_spec _ _ _ _).1, (fillLevel_spec _ _ _ _).1, ← i1]
      unfold prj1
      split_ifs <;> rfl
    · funext k j
      show ((fillLevel (treeBuild2 n fl fu v0 K).1 (K + 1) _ (2 ^ (n - (K + 1)))).1 k j).2
        = (fillLevel (treeBuild n fu (prj2 v0) K).1 (K + 1)
            (fun j => (treeBuild n fu (prj2 v0) K).1 K (2 * j)
              ⊔ (treeBuild n fu (prj2 v0) K).1 K (2 * j + 1)) (2 ^ (n - (K + 1)))).1 k j
      rw [(fillLevel_spec _ _ _ _).1, (fillLevel_spec _ _ _ _).1, ← i2]
      unfold prj2
      split_ifs <;> rfl
    · show (treeBuild2 n fl fu v0 K).2 + (fillLevel _ (K + 1) _ (2 ^ (n - (K + 1)))).2
        = (treeBuild n fl (prj1 v0) K).2 + (fillLevel _ (K + 1) _ (2 ^ (n - (K + 1)))).2
      rw [i3, (fillLevel_spec _ _ _ _).2, (fillLevel_spec _ _ _ _).2]

end Shared

/-! ## The index: state, update -/

section Index

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]
  {Γ : Type*} [LinearOrder Γ] [OrderBot Γ]

/-- State of the dual-cover index: ONE shared segment-tree array whose nodes hold the pair
(lower maximum, upper maximum); per root action an indexed max-heap on the lower maxima of
the blocks of `C_a⁺` and one on the upper maxima of the blocks of `C_a⁻`; ONE global indexed
heap over the root actions; and the mark array used to build the affected-action list. -/
structure IState (A α Γ : Type*) where
  tree : ℕ → ℕ → α × α
  hpP : A → Heap (ℕ × ℕ) α
  hpM : A → Heap (ℕ × ℕ) α
  gh : Heap A Γ
  mark : A → Bool

omit [OrderBot α] [DecidableEq A] in
/-- A subscribed block that is not a changed subscription keeps its tree value. -/
lemma path_stable (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A)
    (hsub : ∀ a, ∀ d ∈ cov a, a ∈ subs d) (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n) (p : ℕ) (x : α)
    (tr : ℕ → ℕ → α) (a : A) (d : ℕ × ℕ) (hd : d ∈ cov a)
    (hn : (d, a) ∉ changedSubs n subs p x tr) :
    (pathUpdate p x tr n).1 d.1 d.2 = tr d.1 d.2 := by
  by_cases hj : d.2 = p / 2 ^ d.1
  · by_contra hne
    exact hn ((mem_changedSubs n subs p x tr d a).2
      ⟨(mem_changedNodes p tr _ n d.1 d.2).2 ⟨hlev a d hd, hj, hne⟩, hsub a d hd⟩)
  · exact pathUpdate_off p x tr n d.1 d.2 hj

omit [OrderBot α] in
/-- Deliveries of the changed subscriptions of one endpoint family: afterwards every action
heap stores the new tree values of its blocks. -/
lemma deliver_rep (n : ℕ) (cov : A → Finset (ℕ × ℕ)) (subs : ℕ × ℕ → List A) (b : A → ℕ)
    (hsub : ∀ a, ∀ d ∈ cov a, a ∈ subs d) (hlev : ∀ a, ∀ d ∈ cov a, d.1 ≤ n) (p : ℕ) (x : α)
    (tr : ℕ → ℕ → α) (hp : A → Heap (ℕ × ℕ) α)
    (hrep : ∀ a, Rep (hp a) (cov a) (fun d => tr d.1 d.2) (b a)) :
    (∀ a, Rep ((deliverH (pathUpdate p x tr n).1 (changedSubs n subs p x tr) hp).1 a) (cov a)
      (fun d => (pathUpdate p x tr n).1 d.1 d.2) (b a)) ∧
    (deliverH (pathUpdate p x tr n).1 (changedSubs n subs p x tr) hp).2
      ≤ ((changedSubs n subs p x tr).map (fun e => Nat.clog 2 (b e.2) + 2)).sum := by
  obtain ⟨h1, h2⟩ := deliverH_spec (pathUpdate p x tr n).1 cov b (changedSubs n subs p x tr) hp
    (fun _ d => tr d.1 d.2) hrep
  refine ⟨fun a => (h1 a).congr (fun d hd => ?_), h2⟩
  rw [deliver_key]
  split_ifs with hin
  · rfl
  · exact (path_stable n cov subs hsub hlev p x tr a d hd hin).symm

/-- **Refresh of the global heap**: for each affected action read the roots of its two
heaps (2 units), form its key `gk U⁻ L a` (1 unit) and update the key in the global heap
(`HeapImpl.updateKey`, computed cost). -/
def refreshG (gk : α → α → A → Γ) (hpP hpM : A → Heap (ℕ × ℕ) α) :
    List A → Heap A Γ → Heap A Γ × ℕ
  | [], gh => (gh, 0)
  | a :: rest, gh =>
    ((refreshG gk hpP hpM rest
        (updateKey gh a (gk (findMax (hpM a)) (findMax (hpP a)) a)).1).1,
     (refreshG gk hpP hpM rest
        (updateKey gh a (gk (findMax (hpM a)) (findMax (hpP a)) a)).1).2
       + (updateKey gh a (gk (findMax (hpM a)) (findMax (hpP a)) a)).2 + 3)

omit [OrderBot Γ] in
theorem refreshG_spec (gk : α → α → A → Γ) (hpP hpM : A → Heap (ℕ × ℕ) α) (acts : Finset A)
    (K : ℕ) : ∀ (L : List A) (gh : Heap A Γ) (k : A → Γ), Rep gh acts k K →
    Rep (refreshG gk hpP hpM L gh).1 acts
      (fun a => if a ∈ L then gk (findMax (hpM a)) (findMax (hpP a)) a else k a) K ∧
    (refreshG gk hpP hpM L gh).2 ≤ L.length * (Nat.clog 2 K + 5) := by
  intro L
  induction L with
  | nil => intro gh k h; exact ⟨h.congr (fun a _ => by simp), by simp [refreshG]⟩
  | cons b rest ih =>
    intro gh k h
    have hstep := h.update b (gk (findMax (hpM b)) (findMax (hpP b)) b)
    obtain ⟨h1, h2⟩ := ih _ _ hstep
    refine ⟨h1.congr (fun a _ => ?_), ?_⟩
    · simp only [List.mem_cons]
      by_cases h3 : a ∈ rest
      · simp [h3]
      · by_cases h4 : a = b
        · rw [h4]; simp
        · simp [h3, h4]
    · have hc := h.updateKey_cost b (gk (findMax (hpM b)) (findMax (hpP b)) b)
      simp only [refreshG, List.length_cons]
      have : (rest.length + 1) * (Nat.clog 2 K + 5)
          = rest.length * (Nat.clog 2 K + 5) + (Nat.clog 2 K + 5) := by ring
      omega

/-- **One terminal update of the index**: the terminal at layout position `p` receives the
interval `[x, y]`.

1. shared tree: recompute the path (`pathUpdate2`);
2. change detection on the path, separately for the two fields (`CostModel.changedNodes`);
3. construction of the changed-subscription lists `𝒩_t⁺`, `𝒩_t⁻` (`subsList`);
4. one heap key update per changed subscription (`HeapImpl.deliverH`);
5. construction of the affected-action list `𝒜_t` with the mark array (`collect`);
6. one update of the global heap per affected action (`refreshG`);
7. clearing of the marks (`clearMarks`).

The cost is the sum of the computed costs of the seven stages. -/
def iUpdate (n : ℕ) (subsP subsM : ℕ × ℕ → List A) (gk : α → α → A → Γ) (p : ℕ) (x y : α)
    (s : IState A α Γ) : IState A α Γ × ℕ :=
  let t' := pathUpdate2 p x y s.tree n
  let cP := changedNodes p (prj1 s.tree) (prj1 t'.1) n
  let cM := changedNodes p (prj2 s.tree) (prj2 t'.1) n
  let nP := subsList subsP cP.1
  let nM := subsList subsM cM.1
  let dP := deliverH (prj1 t'.1) nP.1 s.hpP
  let dM := deliverH (prj2 t'.1) nM.1 s.hpM
  let c1 := collect nP.1 s.mark []
  let c2 := collect nM.1 c1.1.1 c1.1.2
  let g := refreshG gk dP.1 dM.1 c2.1.2 s.gh
  let m := clearMarks c2.1.2 c2.1.1
  (⟨t'.1, dP.1, dM.1, g.1, m.1⟩,
   t'.2 + cP.2 + cM.2 + nP.2 + nM.2 + dP.2 + dM.2 + c1.2 + c2.2 + g.2 + m.2)

/-- Invariant of the index for the terminal box `[l, u]`: the two fields of every tree node
of level at most `n` are the block maxima of `l` and of `u`; the heaps of action `a` store
the lower maxima of the blocks of `C_a⁺` and the upper maxima of the blocks of `C_a⁻`; the
global heap stores for every root action the key `gk U⁻(a) L(a) a` formed from the maxima
of these heaps; no action is marked. -/
structure IInv (n : ℕ) (covP covM : A → Finset (ℕ × ℕ)) (bP bM : A → ℕ) (acts : Finset A)
    (K : ℕ) (gk : α → α → A → Γ) (l u : ℕ → α) (s : IState A α Γ) : Prop where
  treeP : ∀ k ≤ n, ∀ j, prj1 s.tree k j = (dyadicBlock k j).sup l
  treeM : ∀ k ≤ n, ∀ j, prj2 s.tree k j = (dyadicBlock k j).sup u
  hpP : ∀ a, Rep (s.hpP a) (covP a) (fun d => prj1 s.tree d.1 d.2) (bP a)
  hpM : ∀ a, Rep (s.hpM a) (covM a) (fun d => prj2 s.tree d.1 d.2) (bM a)
  gh : Rep s.gh acts (fun a => gk ((covM a).sup (fun d => prj2 s.tree d.1 d.2))
    ((covP a).sup (fun d => prj1 s.tree d.1 d.2)) a) K
  mark : ∀ a, s.mark a = false

/-- The update terms of `eq:dual-cover-work` for one update, with explicit constant:

`7 · ( h + Σ_{(d,a) ∈ 𝒩_t⁺} ⌈log₂(2 + b_a⁺)⌉ + Σ_{(d,a) ∈ 𝒩_t⁻} ⌈log₂(2 + b_a⁻)⌉
       + |𝒜_t| ⌈log₂(2 + K)⌉ )`,

where `h = n + 1`, `𝒩_t⁺ = changedSubs` of the lower field (pairs of a block whose lower
maximum changes and an action subscribed to it in `C⁺`), `𝒩_t⁻` likewise for the upper
field, and `𝒜_t` is the set of actions occurring in `𝒩_t⁺ ∪ 𝒩_t⁻`. -/
def updCost (n : ℕ) (subsP subsM : ℕ × ℕ → List A) (bP bM : A → ℕ) (K p : ℕ) (x y : α)
    (tP tM : ℕ → ℕ → α) : ℕ :=
  7 * ((n + 1)
    + ((changedSubs n subsP p x tP).map (fun e => Nat.clog 2 (2 + bP e.2))).sum
    + ((changedSubs n subsM p y tM).map (fun e => Nat.clog 2 (2 + bM e.2))).sum
    + ((changedSubs n subsP p x tP).map Prod.snd
        ++ (changedSubs n subsM p y tM).map Prod.snd).toFinset.card * Nat.clog 2 (2 + K))

lemma clog_two_add (b : ℕ) : 1 ≤ Nat.clog 2 (2 + b) ∧ Nat.clog 2 b ≤ Nat.clog 2 (2 + b) :=
  ⟨Nat.clog_pos (by norm_num) (by omega), Nat.clog_mono_right 2 (by omega)⟩

omit [DecidableEq A] in
lemma sum_log_bound (b : A → ℕ) : ∀ L : List ((ℕ × ℕ) × A),
    (L.map (fun e => Nat.clog 2 (b e.2) + 2)).sum + 2 * L.length
      ≤ 5 * (L.map (fun e => Nat.clog 2 (2 + b e.2))).sum := by
  intro L
  induction L with
  | nil => simp
  | cons e L ih =>
    obtain ⟨h1, h2⟩ := clog_two_add (b e.2)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

omit [OrderBot Γ] in
/-- **Correctness and cost of one update.**  If the reverse-subscription lists contain
every subscription and the cover blocks are tree nodes of level at most `n`, the update
maps the invariant for `[l, u]` to the invariant for the box with position `p` set to
`[x, y]`, and its computed cost is at most `updCost`. -/
theorem iUpdate_spec (n : ℕ) (covP covM : A → Finset (ℕ × ℕ)) (subsP subsM : ℕ × ℕ → List A)
    (bP bM : A → ℕ) (acts : Finset A) (K : ℕ) (gk : α → α → A → Γ)
    (hsubP : ∀ a, ∀ d ∈ covP a, a ∈ subsP d) (hlevP : ∀ a, ∀ d ∈ covP a, d.1 ≤ n)
    (hsubM : ∀ a, ∀ d ∈ covM a, a ∈ subsM d) (hlevM : ∀ a, ∀ d ∈ covM a, d.1 ≤ n)
    (p : ℕ) (x y : α) (l u : ℕ → α) (s : IState A α Γ)
    (inv : IInv n covP covM bP bM acts K gk l u s) :
    IInv n covP covM bP bM acts K gk (Function.update l p x) (Function.update u p y)
      (iUpdate n subsP subsM gk p x y s).1 ∧
    (iUpdate n subsP subsM gk p x y s).2
      ≤ updCost n subsP subsM bP bM K p x y (prj1 s.tree) (prj2 s.tree) := by
  obtain ⟨e1, e2, e3⟩ := pathUpdate2_prj p x y s.tree n
  have hNP := subsList_spec subsP
    (changedNodes p (prj1 s.tree) (pathUpdate p x (prj1 s.tree) n).1 n).1
  have hNM := subsList_spec subsM
    (changedNodes p (prj2 s.tree) (pathUpdate p y (prj2 s.tree) n).1 n).1
  have hNP1 : (subsList subsP
      (changedNodes p (prj1 s.tree) (pathUpdate p x (prj1 s.tree) n).1 n).1).1
      = changedSubs n subsP p x (prj1 s.tree) := hNP.1
  have hNM1 : (subsList subsM
      (changedNodes p (prj2 s.tree) (pathUpdate p y (prj2 s.tree) n).1 n).1).1
      = changedSubs n subsM p y (prj2 s.tree) := hNM.1
  rw [hNP1] at hNP
  rw [hNM1] at hNM
  obtain ⟨dP1, dP2⟩ := deliver_rep n covP subsP bP hsubP hlevP p x (prj1 s.tree) s.hpP inv.hpP
  obtain ⟨dM1, dM2⟩ := deliver_rep n covM subsM bM hsubM hlevM p y (prj2 s.tree) s.hpM inv.hpM
  obtain ⟨a1, a2, a3, a4⟩ := collect_spec (changedSubs n subsP p x (prj1 s.tree)) s.mark []
    (fun a => by simp [inv.mark a]) List.nodup_nil
  obtain ⟨b1, b2, b3, b4⟩ := collect_spec (changedSubs n subsM p y (prj2 s.tree)) _ _ a1 a2
  obtain ⟨g1, g2⟩ := refreshG_spec gk
    (deliverH (pathUpdate p x (prj1 s.tree) n).1 (changedSubs n subsP p x (prj1 s.tree))
      s.hpP).1
    (deliverH (pathUpdate p y (prj2 s.tree) n).1 (changedSubs n subsM p y (prj2 s.tree))
      s.hpM).1 acts K
    (collect (changedSubs n subsM p y (prj2 s.tree))
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.2 s.gh _ inv.gh
  obtain ⟨m1, m2⟩ := clearMarks_spec
    (collect (changedSubs n subsM p y (prj2 s.tree))
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.2
    (collect (changedSubs n subsM p y (prj2 s.tree))
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.1
  have hmem : ∀ a, a ∈ (collect (changedSubs n subsM p y (prj2 s.tree))
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.2
      ↔ a ∈ (changedSubs n subsP p x (prj1 s.tree)).map Prod.snd
        ∨ a ∈ (changedSubs n subsM p y (prj2 s.tree)).map Prod.snd := by
    intro a
    rw [b3 a, a3 a]
    simp
  have hlen : (collect (changedSubs n subsM p y (prj2 s.tree))
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.2.length
      = ((changedSubs n subsP p x (prj1 s.tree)).map Prod.snd
        ++ (changedSubs n subsM p y (prj2 s.tree)).map Prod.snd).toFinset.card := by
    rw [← List.toFinset_card_of_nodup b2]
    congr 1
    ext a
    rw [List.mem_toFinset, List.mem_toFinset, hmem a, List.mem_append]
  simp only [iUpdate]
  rw [e1, e2, hNP1, hNM1]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k hk j
    show prj1 (pathUpdate2 p x y s.tree n).1 k j = _
    rw [e1]
    exact pathUpdate_spec p x l _ n inv.treeP k hk j
  · intro k hk j
    show prj2 (pathUpdate2 p x y s.tree n).1 k j = _
    rw [e2]
    exact pathUpdate_spec p y u _ n inv.treeM k hk j
  · intro a
    show Rep _ (covP a) (fun d => prj1 (pathUpdate2 p x y s.tree n).1 d.1 d.2) (bP a)
    rw [e1]
    exact dP1 a
  · intro a
    show Rep _ (covM a) (fun d => prj2 (pathUpdate2 p x y s.tree n).1 d.1 d.2) (bM a)
    rw [e2]
    exact dM1 a
  · show Rep _ acts (fun a => gk
      ((covM a).sup (fun d => prj2 (pathUpdate2 p x y s.tree n).1 d.1 d.2))
      ((covP a).sup (fun d => prj1 (pathUpdate2 p x y s.tree n).1 d.1 d.2)) a) K
    rw [e1, e2]
    refine g1.congr (fun a _ => ?_)
    by_cases ha : a ∈ (collect (changedSubs n subsM p y (prj2 s.tree))
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
      (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.2
    · rw [ite_eq_left ha, (dP1 a).findMax, (dM1 a).findMax]
    · rw [ite_eq_right ha]
      have hno := (not_congr (hmem a)).1 ha
      rw [not_or] at hno
      have hP : (covP a).sup (fun d => prj1 s.tree d.1 d.2)
          = (covP a).sup (fun d => (pathUpdate p x (prj1 s.tree) n).1 d.1 d.2) :=
        Finset.sup_congr rfl (fun d hd =>
          (path_stable n covP subsP hsubP hlevP p x _ a d hd
            (fun hin => hno.1 (List.mem_map.2 ⟨(d, a), hin, rfl⟩))).symm)
      have hM : (covM a).sup (fun d => prj2 s.tree d.1 d.2)
          = (covM a).sup (fun d => (pathUpdate p y (prj2 s.tree) n).1 d.1 d.2) :=
        Finset.sup_congr rfl (fun d hd =>
          (path_stable n covM subsM hsubM hlevM p y _ a d hd
            (fun hin => hno.2 (List.mem_map.2 ⟨(d, a), hin, rfl⟩))).symm)
      rw [hP, hM]
  · intro a
    show (clearMarks _ _).1 a = false
    rw [m1 a]
    split_ifs with ha
    · rfl
    · have := (not_congr (b1 a)).2 ha
      simpa using this
  · have c1 := changedNodes_cost p (prj1 s.tree) (pathUpdate p x (prj1 s.tree) n).1 n
    have c2 := changedNodes_cost p (prj2 s.tree) (pathUpdate p y (prj2 s.tree) n).1 n
    have l1 := changedNodes_length p (prj1 s.tree) (pathUpdate p x (prj1 s.tree) n).1 n
    have l2 := changedNodes_length p (prj2 s.tree) (pathUpdate p y (prj2 s.tree) n).1 n
    have s1 := sum_log_bound bP (changedSubs n subsP p x (prj1 s.tree))
    have s2 := sum_log_bound bM (changedSubs n subsM p y (prj2 s.tree))
    have hK := clog_two_add K
    have hG : (collect (changedSubs n subsM p y (prj2 s.tree))
        (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
        (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.2.length
          * (Nat.clog 2 K + 5)
        + (collect (changedSubs n subsM p y (prj2 s.tree))
        (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.1
        (collect (changedSubs n subsP p x (prj1 s.tree)) s.mark []).1.2).1.2.length
        ≤ 7 * (((changedSubs n subsP p x (prj1 s.tree)).map Prod.snd
          ++ (changedSubs n subsM p y (prj2 s.tree)).map Prod.snd).toFinset.card
            * Nat.clog 2 (2 + K)) := by
      rw [hlen]
      have : Nat.clog 2 K + 5 + 1 ≤ 7 * Nat.clog 2 (2 + K) := by omega
      calc _ = ((changedSubs n subsP p x (prj1 s.tree)).map Prod.snd
            ++ (changedSubs n subsM p y (prj2 s.tree)).map Prod.snd).toFinset.card
              * (Nat.clog 2 K + 5 + 1) := by ring
        _ ≤ ((changedSubs n subsP p x (prj1 s.tree)).map Prod.snd
            ++ (changedSubs n subsM p y (prj2 s.tree)).map Prod.snd).toFinset.card
              * (7 * Nat.clog 2 (2 + K)) := Nat.mul_le_mul_left _ this
        _ = _ := by ring
    unfold updCost
    omega

end Index

/-! ## Initialisation in linear time -/

section Init

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A] [Inhabited A]
  {Γ : Type*} [LinearOrder Γ] [OrderBot Γ]

/-- Build the heaps of one endpoint family for the root actions in turn.  Per action: read
the tree value of every block of its cover (1 unit each), build the heap bottom-up
(`LiteralK7a.build`, computed cost), register one reverse subscription per block (1 unit
each), and one unit for the heap record. -/
def initHeapsL (tr : ℕ → ℕ → α) (covL : A → List (ℕ × ℕ)) :
    List A → (A → Heap (ℕ × ℕ) α) → (A → Heap (ℕ × ℕ) α) × ℕ
  | [], hp => (hp, 0)
  | a :: as, hp =>
    ((initHeapsL tr covL as (Function.update hp a
        (LiteralK7a.build (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).1).1)).1,
     (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).2
      + (LiteralK7a.build (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).1).2
      + (covL a).length + 1
      + (initHeapsL tr covL as (Function.update hp a
        (LiteralK7a.build (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).1).1)).2)

omit [Inhabited A] in
lemma initHeapsL_spec (tr : ℕ → ℕ → α) (covL : A → List (ℕ × ℕ))
    (hcn : ∀ a, (covL a).Nodup) : ∀ (as : List A) (hp : A → Heap (ℕ × ℕ) α), as.Nodup →
    (∀ a ∈ as, Rep ((initHeapsL tr covL as hp).1 a) (covL a).toFinset (fun d => tr d.1 d.2)
      (covL a).length) ∧
    (∀ a, a ∉ as → (initHeapsL tr covL as hp).1 a = hp a) ∧
    (initHeapsL tr covL as hp).2 ≤ (as.map (fun a => 8 * (covL a).length + 1)).sum := by
  have hb : ∀ a, Rep (LiteralK7a.build (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).1).1
      (covL a).toFinset (fun d => tr d.1 d.2) (covL a).length ∧
      (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).2
        + (LiteralK7a.build (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).1).2
        ≤ 7 * (covL a).length := by
    intro a
    obtain ⟨c1, c2⟩ := cmap_spec (fun d : ℕ × ℕ => (d, tr d.1 d.2)) 1 (covL a)
    obtain ⟨b1, _, b3⟩ := LiteralK7a.build_spec (covL a) (hcn a) (fun d => tr d.1 d.2)
    rw [c1, c2]
    exact ⟨b1, by omega⟩
  intro as
  induction as with
  | nil => intro hp _; exact ⟨fun a ha => by simp at ha, fun _ _ => rfl, by simp [initHeapsL]⟩
  | cons a as ih =>
    intro hp hnd
    rw [List.nodup_cons] at hnd
    obtain ⟨i1, i2, i3⟩ := ih (Function.update hp a
      (LiteralK7a.build (cmap (fun d => (d, tr d.1 d.2)) 1 (covL a)).1).1) hnd.2
    refine ⟨fun b hb' => ?_, fun b hb' => ?_, ?_⟩
    · show Rep ((initHeapsL tr covL as _).1 b) _ _ _
      by_cases e : b = a
      · rw [e, i2 a hnd.1, Function.update_self]
        exact (hb a).1
      · rcases List.mem_cons.1 hb' with h | h
        · exact absurd h e
        · exact i1 b h
    · show (initHeapsL tr covL as _).1 b = _
      rw [List.mem_cons, not_or] at hb'
      rw [i2 b hb'.2, Function.update_of_ne hb'.1]
    · have := (hb a).2
      show _ + _ + (covL a).length + 1 + (initHeapsL tr covL as _).2 ≤ _
      rw [List.map_cons, List.sum_cons]
      omega

/-- **Initialisation of the index**: build the shared tree from the initial box `[fl, fu]`
(`treeBuild2`), the two heaps of every root action (`initHeapsL`), form the key of every
action (3 units each: two root reads and the key), build the global heap bottom-up
(`LiteralK7a.build`), and clear the mark array (1 unit per action). -/
def iInit (n : ℕ) (fl fu : ℕ → α) (covPL covML : A → List (ℕ × ℕ)) (gk : α → α → A → Γ)
    (as : List A) : IState A α Γ × ℕ :=
  let t := treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n
  let hP := initHeapsL (prj1 t.1) covPL as (fun _ => Heap.empty)
  let hM := initHeapsL (prj2 t.1) covML as (fun _ => Heap.empty)
  let ks := cmap (fun a => (a, gk (findMax (hM.1 a)) (findMax (hP.1 a)) a)) 3 as
  let g := LiteralK7a.build ks.1
  (⟨t.1, hP.1, hM.1, g.1, fun _ => false⟩, t.2 + hP.2 + hM.2 + ks.2 + g.2 + as.length)

/-- **Correctness and linear cost of the initialisation** (the `M + B + K` terms of
`eq:dual-cover-work`).  With initial values blank beyond `2^n`, root actions `as` without
repetition, cover lists without repeated blocks and empty for non-actions, the initial
state satisfies the index invariant for the box `[fl, fu]`, tree cells above level `n` are
blank, and the computed cost is at most

`(2^(n+1) - 1) + Σ_a (8 b_a⁺ + 1) + Σ_a (8 b_a⁻ + 1) + 10 K`. -/
theorem iInit_spec (n : ℕ) (fl fu : ℕ → α) (hfl : ∀ p, 2 ^ n ≤ p → fl p = ⊥)
    (hfu : ∀ p, 2 ^ n ≤ p → fu p = ⊥) (covPL covML : A → List (ℕ × ℕ))
    (gk : α → α → A → Γ) (as : List A) (hnd : as.Nodup)
    (hcP : ∀ a, (covPL a).Nodup) (hcM : ∀ a, (covML a).Nodup)
    (hoP : ∀ a, a ∉ as → covPL a = []) (hoM : ∀ a, a ∉ as → covML a = []) :
    IInv n (fun a => (covPL a).toFinset) (fun a => (covML a).toFinset)
      (fun a => (covPL a).length) (fun a => (covML a).length) as.toFinset as.length gk fl fu
      (iInit n fl fu covPL covML gk as).1 ∧
    (∀ k, n < k → ∀ j, (iInit n fl fu covPL covML gk as).1.tree k j = (⊥, ⊥)) ∧
    (iInit n fl fu covPL covML gk as).2
      ≤ (2 ^ (n + 1) - 1) + (as.map (fun a => 8 * (covPL a).length + 1)).sum
        + (as.map (fun a => 8 * (covML a).length + 1)).sum + 10 * as.length := by
  obtain ⟨p1, p2, p3⟩ := treeBuild2_prj n fl fu (fun _ _ => ((⊥ : α), (⊥ : α))) n
  have q1 : prj1 (fun (_ _ : ℕ) => ((⊥ : α), (⊥ : α))) = fun _ _ => ⊥ := rfl
  have q2 : prj2 (fun (_ _ : ℕ) => ((⊥ : α), (⊥ : α))) = fun _ _ => ⊥ := rfl
  rw [q1] at p1 p3
  rw [q2] at p2
  obtain ⟨t1, t2, t3⟩ := treeBuild_spec n fl hfl n le_rfl
  obtain ⟨u1, u2, _⟩ := treeBuild_spec n fu hfu n le_rfl
  obtain ⟨h1, h2, h3⟩ := initHeapsL_spec (prj1 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
    covPL hcP as (fun _ => Heap.empty) hnd
  obtain ⟨k1, k2, k3⟩ := initHeapsL_spec (prj2 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
    covML hcM as (fun _ => Heap.empty) hnd
  have hrP : ∀ a, Rep ((initHeapsL (prj1 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
      covPL as (fun _ => Heap.empty)).1 a) (covPL a).toFinset
      (fun d => prj1 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 d.1 d.2)
      (covPL a).length := by
    intro a
    by_cases ha : a ∈ as
    · exact h1 a ha
    · rw [h2 a ha, hoP a ha]
      exact ⟨Heap.empty_inv, le_rfl, fun _ => rfl⟩
  have hrM : ∀ a, Rep ((initHeapsL (prj2 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
      covML as (fun _ => Heap.empty)).1 a) (covML a).toFinset
      (fun d => prj2 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 d.1 d.2)
      (covML a).length := by
    intro a
    by_cases ha : a ∈ as
    · exact k1 a ha
    · rw [k2 a ha, hoM a ha]
      exact ⟨Heap.empty_inv, le_rfl, fun _ => rfl⟩
  obtain ⟨c1, c2⟩ := cmap_spec (fun a => (a, gk
    (findMax ((initHeapsL (prj2 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
      covML as (fun _ => Heap.empty)).1 a))
    (findMax ((initHeapsL (prj1 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
      covPL as (fun _ => Heap.empty)).1 a)) a)) 3 as
  obtain ⟨b1, _, b3⟩ := LiteralK7a.build_spec as hnd (fun a => gk
    (findMax ((initHeapsL (prj2 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
      covML as (fun _ => Heap.empty)).1 a))
    (findMax ((initHeapsL (prj1 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1)
      covPL as (fun _ => Heap.empty)).1 a)) a)
  simp only [iInit]
  rw [c1, c2]
  refine ⟨⟨?_, ?_, hrP, hrM, ?_, fun _ => rfl⟩, ?_, ?_⟩
  · intro k hk j
    show prj1 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 k j = _
    rw [p1]
    exact t1 k hk j
  · intro k hk j
    show prj2 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 k j = _
    rw [p2]
    exact u1 k hk j
  · refine b1.congr (fun a _ => ?_)
    rw [(hrP a).findMax, (hrM a).findMax]
  · intro k hk j
    have e1 : ((treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 k j).1 = ⊥ := by
      show prj1 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 k j = ⊥
      rw [p1]
      exact t2 k hk j
    have e2 : ((treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 k j).2 = ⊥ := by
      show prj2 (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).1 k j = ⊥
      rw [p2]
      exact u2 k hk j
    exact Prod.ext e1 e2
  · have ht : (treeBuild2 n fl fu (fun _ _ => (⊥, ⊥)) n).2 = 2 ^ (n + 1) - 1 := by
      rw [p3, t3, segTree_nodes]
    rw [ht]
    omega

end Init

/-! ## Runs of updates and queries -/

section Run

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]
  {Γ : Type*} [LinearOrder Γ] [OrderBot Γ]

/-- **The specification reply, computed directly from the terminal box** `[l, u]`: the
maximum in the key order `Γ` over the root actions `a` of the key `gk U⁻(a) L(a) a`, where
`L(a) = max_{z ∈ SP a} l(z)` and `U⁻(a) = max_{z ∈ SM a} u(z)` (`SP a` the support of `a`,
`SM a` its complement). -/
def boxReply (acts : Finset A) (gk : α → α → A → Γ) (SP SM : A → Finset ℕ) (l u : ℕ → α) : Γ :=
  acts.sup (fun a => gk ((SM a).sup u) ((SP a).sup l) a)

/-- A run of operations on the index: `some (p, x, y)` is a terminal update, `none` a
minimiser query.  A query reads the root of the global heap (`findMax`, one array read):
one unit.  Returns the final state, the list of replies and the computed cost. -/
def iRun (n : ℕ) (subsP subsM : ℕ × ℕ → List A) (gk : α → α → A → Γ) :
    List (Option (ℕ × α × α)) → IState A α Γ → (IState A α Γ × List Γ) × ℕ
  | [], s => ((s, []), 0)
  | none :: ops, s =>
    (((iRun n subsP subsM gk ops s).1.1, findMax s.gh :: (iRun n subsP subsM gk ops s).1.2),
     (iRun n subsP subsM gk ops s).2 + 1)
  | some o :: ops, s =>
    ((iRun n subsP subsM gk ops (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).1).1,
     (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).2
      + (iRun n subsP subsM gk ops (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).1).2)

/-- The replies of the specification along a run. -/
def specRun (acts : Finset A) (gk : α → α → A → Γ) (SP SM : A → Finset ℕ) :
    List (Option (ℕ × α × α)) → (ℕ → α) → (ℕ → α) → List Γ
  | [], _, _ => []
  | none :: ops, l, u => boxReply acts gk SP SM l u :: specRun acts gk SP SM ops l u
  | some o :: ops, l, u =>
    specRun acts gk SP SM ops (Function.update l o.1 o.2.1) (Function.update u o.1 o.2.2)

/-- The terminal box after a run. -/
def boxRun : List (Option (ℕ × α × α)) → (ℕ → α) → (ℕ → α) → (ℕ → α) × (ℕ → α)
  | [], l, u => (l, u)
  | none :: ops, l, u => boxRun ops l u
  | some o :: ops, l, u =>
    boxRun ops (Function.update l o.1 o.2.1) (Function.update u o.1 o.2.2)

/-- Number of queries of a run. -/
def numQ : List (Option (ℕ × α × α)) → ℕ
  | [] => 0
  | none :: ops => numQ ops + 1
  | some _ :: ops => numQ ops

/-- The update terms of `eq:dual-cover-work` summed along a run, starting from the tree
fields `tP`, `tM`: `Σ_t updCost_t` (queries contribute nothing). -/
def runSum (n : ℕ) (subsP subsM : ℕ × ℕ → List A) (bP bM : A → ℕ) (K : ℕ) :
    List (Option (ℕ × α × α)) → (ℕ → ℕ → α) → (ℕ → ℕ → α) → ℕ
  | [], _, _ => 0
  | none :: ops, tP, tM => runSum n subsP subsM bP bM K ops tP tM
  | some o :: ops, tP, tM =>
    updCost n subsP subsM bP bM K o.1 o.2.1 o.2.2 tP tM
      + runSum n subsP subsM bP bM K ops (pathUpdate o.1 o.2.1 tP n).1
          (pathUpdate o.1 o.2.2 tM n).1

/-- **Minimiser query**: under the invariant the root of the global heap is the
specification reply for the current box. -/
theorem query_reply {n : ℕ} {covP covM : A → Finset (ℕ × ℕ)} {bP bM : A → ℕ}
    {acts : Finset A} {K : ℕ} {gk : α → α → A → Γ} {l u : ℕ → α} {s : IState A α Γ}
    (inv : IInv n covP covM bP bM acts K gk l u s)
    (hlevP : ∀ a, ∀ d ∈ covP a, d.1 ≤ n) (hlevM : ∀ a, ∀ d ∈ covM a, d.1 ≤ n) :
    findMax s.gh = boxReply acts gk (fun a => (covP a).biUnion blk)
      (fun a => (covM a).biUnion blk) l u := by
  rw [inv.gh.findMax]
  unfold boxReply
  apply Finset.sup_congr rfl
  intro a _
  have hP : (covP a).sup (fun d => prj1 s.tree d.1 d.2) = ((covP a).biUnion blk).sup l := by
    rw [Finset.sup_biUnion]
    apply Finset.sup_congr rfl
    intro d hd
    rw [inv.treeP d.1 (hlevP a d hd) d.2]
    rfl
  have hM : (covM a).sup (fun d => prj2 s.tree d.1 d.2) = ((covM a).biUnion blk).sup u := by
    rw [Finset.sup_biUnion]
    apply Finset.sup_congr rfl
    intro d hd
    rw [inv.treeM d.1 (hlevM a d hd) d.2]
    rfl
  rw [hP, hM]

/-- **A run of updates and queries.**  From a state satisfying the invariant for `[l, u]`:
every query returns the specification reply for the box at that time; the final state
satisfies the invariant for the final box; and the computed cost is at most the sum of the
update terms plus one unit per query. -/
theorem iRun_spec (n : ℕ) (covP covM : A → Finset (ℕ × ℕ)) (subsP subsM : ℕ × ℕ → List A)
    (bP bM : A → ℕ) (acts : Finset A) (K : ℕ) (gk : α → α → A → Γ)
    (hsubP : ∀ a, ∀ d ∈ covP a, a ∈ subsP d) (hlevP : ∀ a, ∀ d ∈ covP a, d.1 ≤ n)
    (hsubM : ∀ a, ∀ d ∈ covM a, a ∈ subsM d) (hlevM : ∀ a, ∀ d ∈ covM a, d.1 ≤ n) :
    ∀ (ops : List (Option (ℕ × α × α))) (s : IState A α Γ) (l u : ℕ → α),
    IInv n covP covM bP bM acts K gk l u s →
    (iRun n subsP subsM gk ops s).1.2
      = specRun acts gk (fun a => (covP a).biUnion blk) (fun a => (covM a).biUnion blk)
          ops l u ∧
    IInv n covP covM bP bM acts K gk (boxRun ops l u).1 (boxRun ops l u).2
      (iRun n subsP subsM gk ops s).1.1 ∧
    (iRun n subsP subsM gk ops s).2
      ≤ runSum n subsP subsM bP bM K ops (prj1 s.tree) (prj2 s.tree) + numQ ops := by
  intro ops
  induction ops with
  | nil => intro s l u inv; exact ⟨rfl, inv, le_rfl⟩
  | cons o ops ih =>
    intro s l u inv
    cases o with
    | none =>
      obtain ⟨i1, i2, i3⟩ := ih s l u inv
      refine ⟨?_, i2, ?_⟩
      · show findMax s.gh :: (iRun n subsP subsM gk ops s).1.2 = _ :: _
        rw [i1, query_reply inv hlevP hlevM]
      · show (iRun n subsP subsM gk ops s).2 + 1
          ≤ runSum n subsP subsM bP bM K ops (prj1 s.tree) (prj2 s.tree) + (numQ ops + 1)
        omega
    | some o =>
      obtain ⟨v1, v2⟩ := iUpdate_spec n covP covM subsP subsM bP bM acts K gk hsubP hlevP
        hsubM hlevM o.1 o.2.1 o.2.2 l u s inv
      obtain ⟨i1, i2, i3⟩ := ih _ _ _ v1
      obtain ⟨e1, e2, _⟩ := pathUpdate2_prj o.1 o.2.1 o.2.2 s.tree n
      have t1 : prj1 (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).1.tree
          = (pathUpdate o.1 o.2.1 (prj1 s.tree) n).1 := e1
      have t2 : prj2 (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).1.tree
          = (pathUpdate o.1 o.2.2 (prj2 s.tree) n).1 := e2
      rw [t1, t2] at i3
      refine ⟨i1, i2, ?_⟩
      show (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).2
          + (iRun n subsP subsM gk ops (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).1).2
        ≤ updCost n subsP subsM bP bM K o.1 o.2.1 o.2.2 (prj1 s.tree) (prj2 s.tree)
          + runSum n subsP subsM bP bM K ops (pathUpdate o.1 o.2.1 (prj1 s.tree) n).1
              (pathUpdate o.1 o.2.2 (prj2 s.tree) n).1 + numQ ops
      omega

end Run

/-! ## The index as an implementation of the certificate-and-witness oracle -/

section Oracle

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]
  {Γ : Type*} [LinearOrder Γ] [OrderBot Γ] {Z X St Rp : Type*}

/-- **The dual-cover index as an oracle implementation.**  Observations are pairs (sampled
terminal, reward).  The statistics `St` (updated by `stp`) determine the new interval
`iv st z` of the terminal just sampled; one observation is one terminal update of the index
at layout position `pos z`; the reply is the root of the global heap, read through `out`. -/
def dualImpl (n : ℕ) (subsP subsM : ℕ × ℕ → List A) (gk : α → α → A → Γ) (out : Γ → Rp)
    (s0 : IState A α Γ) (st0 : St) (stp : St → Z × X → St) (iv : St → Z → α × α)
    (pos : Z → ℕ) : OracleImpl (St × IState A α Γ) (Z × X) Rp where
  init := (st0, s0)
  step := fun σ o => (stp σ.1 o,
    (iUpdate n subsP subsM gk (pos o.1) (iv (stp σ.1 o) o.1).1 (iv (stp σ.1 o) o.1).2 σ.2).1)
  reply := fun σ => out (findMax σ.2.gh)

/-- **The specification oracle**: it keeps only the statistics and the terminal box, and
computes every reply directly from the box (`boxReply`). -/
def specImpl (acts : Finset A) (gk : α → α → A → Γ) (out : Γ → Rp) (SP SM : A → Finset ℕ)
    (fl fu : ℕ → α) (st0 : St) (stp : St → Z × X → St) (iv : St → Z → α × α) (pos : Z → ℕ) :
    OracleImpl (St × (ℕ → α) × (ℕ → α)) (Z × X) Rp where
  init := (st0, fl, fu)
  step := fun τ o => (stp τ.1 o,
    Function.update τ.2.1 (pos o.1) (iv (stp τ.1 o) o.1).1,
    Function.update τ.2.2 (pos o.1) (iv (stp τ.1 o) o.1).2)
  reply := fun τ => out (boxReply acts gk SP SM τ.2.1 τ.2.2)

/-- **The index exposes the specification oracle**: on every history its answer equals the
answer computed directly from the terminal box. -/
theorem dual_answer_eq (n : ℕ) (covP covM : A → Finset (ℕ × ℕ))
    (subsP subsM : ℕ × ℕ → List A) (bP bM : A → ℕ) (acts : Finset A) (K : ℕ)
    (gk : α → α → A → Γ) (out : Γ → Rp)
    (hsubP : ∀ a, ∀ d ∈ covP a, a ∈ subsP d) (hlevP : ∀ a, ∀ d ∈ covP a, d.1 ≤ n)
    (hsubM : ∀ a, ∀ d ∈ covM a, a ∈ subsM d) (hlevM : ∀ a, ∀ d ∈ covM a, d.1 ≤ n)
    (fl fu : ℕ → α) (s0 : IState A α Γ) (inv : IInv n covP covM bP bM acts K gk fl fu s0)
    (st0 : St) (stp : St → Z × X → St) (iv : St → Z → α × α) (pos : Z → ℕ)
    (h : List (Z × X)) :
    (dualImpl n subsP subsM gk out s0 st0 stp iv pos).answer h
      = (specImpl acts gk out (fun a => (covP a).biUnion blk) (fun a => (covM a).biUnion blk)
          fl fu st0 stp iv pos).answer h := by
  have key : ∀ (h : List (Z × X)) (σ : St × IState A α Γ) (τ : St × (ℕ → α) × (ℕ → α)),
      σ.1 = τ.1 → IInv n covP covM bP bM acts K gk τ.2.1 τ.2.2 σ.2 →
      findMax (h.foldl (dualImpl n subsP subsM gk out s0 st0 stp iv pos).step σ).2.gh
        = boxReply acts gk (fun a => (covP a).biUnion blk) (fun a => (covM a).biUnion blk)
            (h.foldl (specImpl acts gk out (fun a => (covP a).biUnion blk)
              (fun a => (covM a).biUnion blk) fl fu st0 stp iv pos).step τ).2.1
            (h.foldl (specImpl acts gk out (fun a => (covP a).biUnion blk)
              (fun a => (covM a).biUnion blk) fl fu st0 stp iv pos).step τ).2.2 := by
    intro h
    induction h with
    | nil => intro σ τ _ hi; exact query_reply hi hlevP hlevM
    | cons o h ih =>
      intro σ τ hst hi
      rw [List.foldl_cons, List.foldl_cons]
      apply ih
      · show stp σ.1 o = stp τ.1 o
        rw [hst]
      · show IInv n covP covM bP bM acts K gk
          (Function.update τ.2.1 (pos o.1) (iv (stp τ.1 o) o.1).1)
          (Function.update τ.2.2 (pos o.1) (iv (stp τ.1 o) o.1).2)
          (iUpdate n subsP subsM gk (pos o.1) (iv (stp σ.1 o) o.1).1
            (iv (stp σ.1 o) o.1).2 σ.2).1
        rw [hst]
        exact (iUpdate_spec n covP covM subsP subsM bP bM acts K gk hsubP hlevP hsubM hlevM
          _ _ _ _ _ _ hi).1
  show out (findMax _) = out (boxReply _ _ _ _ _ _)
  exact congrArg out (key h (st0, s0) (st0, fl, fu) rfl inv)

end Oracle

/-! ## `P_G` in the form of `eq:dual-run-compilation` -/

section PG

/-- A nonempty position set has at least one run. -/
lemma runs_pos {S : Finset ℕ} (h : S.Nonempty) : 1 ≤ runs S := by
  unfold runs
  refine Finset.card_pos.2 ⟨S.max' h, ?_⟩
  unfold runEnds
  rw [mem_filter]
  refine ⟨S.max'_mem h, fun hm => ?_⟩
  have := S.le_max' _ hm
  omega

/-- Under the support equations every gate of `order` has a nonempty support (derived, not
assumed). -/
theorem supp_nonempty {G : Dag} (hG : G.WF) {pos : ℕ → ℕ} {M : ℕ} {supp : ℕ → Finset ℕ}
    {order : List ℕ} (hclosed : ∀ g ∈ order, ∀ c ∈ G.children g, c ∈ order)
    (hleaf : ∀ g ∈ order, G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order, G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp) :
    ∀ g ∈ order, (supp g).Nonempty := by
  suffices h : ∀ L, ∀ g ∈ order, G.level g < L → (supp g).Nonempty from
    fun g hg => h _ g hg (Nat.lt_succ_self _)
  intro L
  induction L with
  | zero => intro g _ h; omega
  | succ L ih =>
    intro g hg hl
    by_cases hc : G.children g = []
    · rw [(hleaf g hg hc).1]
      exact singleton_nonempty _
    · rw [hgate g hg hc]
      obtain ⟨c, hcm⟩ := List.exists_mem_of_ne_nil _ hc
      have hlt := hG.level_lt g c hcm
      obtain ⟨x, hx⟩ := ih c (hclosed g hg c hcm) (by omega)
      exact ⟨x, mem_biUnion.2 ⟨c, List.mem_toFinset.2 hcm, hx⟩⟩

/-- The term of gate `v` in `eq:dual-run-compilation`:
`P_G = |V| + |E| + Σ_{v ∉ Z} A_v ⌈log₂(2 + |E(v)|)⌉ = Σ_v pgTerm v`, with `A_v` the sum of
the run counts of the children's supports. -/
def pgTerm (G : Dag) (supp : ℕ → Finset ℕ) (g : ℕ) : ℕ :=
  if G.children g = [] then 1
  else 1 + (G.children g).length
    + ((G.children g).map (fun c => runs (supp c))).sum * Nat.clog 2 (2 + (G.children g).length)

/-- The charged run-merging cost of a gate (`RunMerge.gateCost`, pairwise merging) is at
most three times its term in `eq:dual-run-compilation`, provided the children's supports are
nonempty (then `|E(v)| ≤ A_v`). -/
theorem gateCost_le_pgTerm (G : Dag) (supp : ℕ → Finset ℕ) (g : ℕ)
    (hne : ∀ c ∈ G.children g, (supp c).Nonempty) :
    RunMerge.gateCost G supp g ≤ 3 * pgTerm G supp g := by
  unfold RunMerge.gateCost pgTerm
  by_cases hc : G.children g = []
  · rw [ite_eq_left hc, ite_eq_left hc]; omega
  · rw [ite_eq_right hc, ite_eq_right hc]
    have hk : (G.children g).length ≤ ((G.children g).map (fun c => runs (supp c))).sum := by
      have := List.length_le_sum_of_one_le ((G.children g).map (fun c => runs (supp c)))
        (fun i hi => by
          obtain ⟨c, hc', rfl⟩ := List.mem_map.1 hi
          exact runs_pos (hne c hc'))
      rwa [List.length_map] at this
    have hcl : Nat.clog 2 (G.children g).length ≤ Nat.clog 2 (2 + (G.children g).length) :=
      Nat.clog_mono_right 2 (by omega)
    have h1 : Nat.clog 2 (G.children g).length
        * (2 * ((G.children g).map (fun c => runs (supp c))).sum + (G.children g).length)
        ≤ 3 * (((G.children g).map (fun c => runs (supp c))).sum
          * Nat.clog 2 (2 + (G.children g).length)) := by
      calc _ ≤ Nat.clog 2 (2 + (G.children g).length)
            * (3 * ((G.children g).map (fun c => runs (supp c))).sum) :=
            Nat.mul_le_mul hcl (by omega)
        _ = _ := by ring
    omega

/-- **`P_G` of the formal compiler is of the order of `eq:dual-run-compilation`.** -/
theorem PG_le {G : Dag} (hG : G.WF) {pos : ℕ → ℕ} {M : ℕ} {supp : ℕ → Finset ℕ}
    {order : List ℕ} (hclosed : ∀ g ∈ order, ∀ c ∈ G.children g, c ∈ order)
    (hleaf : ∀ g ∈ order, G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order, G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp) :
    (order.map (RunMerge.gateCost G supp)).sum ≤ 3 * (order.map (pgTerm G supp)).sum := by
  have hne := supp_nonempty hG hclosed hleaf hgate
  have key : ∀ l : List ℕ, (∀ g ∈ l, g ∈ order) →
      (l.map (RunMerge.gateCost G supp)).sum ≤ 3 * (l.map (pgTerm G supp)).sum := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons g l ih =>
      intro hl
      simp only [List.map_cons, List.sum_cons]
      have h1 := gateCost_le_pgTerm G supp g
        (fun c hc => hne c (hclosed g (hl g List.mem_cons_self) c hc))
      have h2 := ih (fun g' hg' => hl g' (List.mem_cons_of_mem _ hg'))
      omega
  exact key order (fun _ h => h)

end PG

/-! ## Memory model of the index -/

section Space

variable {α : Type*} [LinearOrder α] [OrderBot α] {A : Type*} [DecidableEq A]
  {Γ : Type*} [LinearOrder Γ] [OrderBot Γ]

/-- **Cells of an implemented heap**: the handle array and the key array of length `n`
(slots `≥ n` are unallocated), and one cell per entry of the handle-to-position map. -/
noncomputable def heapCells {ι β : Type*} (H : Heap ι β) : ℕ :=
  2 * H.n + Set.ncard {h | H.pos h ≠ none}

omit [DecidableEq A] in
lemma posSet_of_rep {ι β : Type*} [DecidableEq ι] [LinearOrder β] [OrderBot β] {H : Heap ι β}
    {S : Finset ι} {k : ι → β} {b : ℕ} (h : Rep H S k b) :
    {x | H.pos x ≠ none} = (S : Set ι) := by
  ext x
  have hl := h.look x
  simp only [HeapImpl.Heap.lookup] at hl
  simp only [Set.mem_ofPred_eq, mem_coe]
  cases hp : H.pos x with
  | none =>
    rw [hp] at hl
    by_cases hx : x ∈ S
    · rw [ite_eq_left hx] at hl
      simp at hl
    · simp [hx]
  | some i =>
    rw [hp] at hl
    by_cases hx : x ∈ S
    · simp [hx]
    · rw [ite_eq_right hx] at hl
      simp at hl

omit [DecidableEq A] in
/-- The handle-to-position map of a heap representing `S` has exactly `|S|` entries. -/
lemma heapCells_rep {ι β : Type*} [DecidableEq ι] [LinearOrder β] [OrderBot β] {H : Heap ι β}
    {S : Finset ι} {k : ι → β} {b : ℕ} (h : Rep H S k b) : heapCells H ≤ 2 * b + S.card := by
  unfold heapCells
  rw [posSet_of_rep h, Set.ncard_coe_finset]
  have := h.size
  omega

/-- The shared tree array fits in the allocated nodes `(k, j)`, `k ≤ n`, `j < 2^(n-k)`:
every other cell holds the blank pair. -/
def TreeFits (n : ℕ) (tree : ℕ → ℕ → α × α) : Prop := ∀ d ∉ nodeSet n, tree d.1 d.2 = (⊥, ⊥)

omit [OrderBot α] in
lemma pathUpdate2_above (p : ℕ) (x y : α) (v : ℕ → ℕ → α × α) (n k j : ℕ) (hk : n < k) :
    (pathUpdate2 p x y v n).1 k j = v k j := by
  obtain ⟨e1, e2, _⟩ := pathUpdate2_prj p x y v n
  have a1 := congrFun (congrFun e1 k) j
  have a2 := congrFun (congrFun e2 k) j
  rw [pathUpdate_above p x (prj1 v) n k j hk] at a1
  rw [pathUpdate_above p y (prj2 v) n k j hk] at a2
  exact Prod.ext a1 a2

/-- Runs never write tree levels above `n`. -/
lemma iRun_tree_above (n : ℕ) (subsP subsM : ℕ × ℕ → List A) (gk : α → α → A → Γ) :
    ∀ (ops : List (Option (ℕ × α × α))) (s : IState A α Γ) (k j : ℕ), n < k →
    (iRun n subsP subsM gk ops s).1.1.tree k j = s.tree k j := by
  intro ops
  induction ops with
  | nil => intro s k j _; rfl
  | cons o ops ih =>
    intro s k j hk
    cases o with
    | none => exact ih s k j hk
    | some o =>
      show (iRun n subsP subsM gk ops (iUpdate n subsP subsM gk o.1 o.2.1 o.2.2 s).1).1.1.tree
        k j = _
      rw [ih _ k j hk]
      exact pathUpdate2_above o.1 o.2.1 o.2.2 s.tree n k j hk

/-- Updates at positions below `N` keep the box blank from `N` on. -/
lemma boxRun_blank (N : ℕ) : ∀ (ops : List (Option (ℕ × α × α))) (l u : ℕ → α),
    (∀ q, some q ∈ ops → q.1 < N) → (∀ p, N ≤ p → l p = ⊥ ∧ u p = ⊥) →
    ∀ p, N ≤ p → (boxRun ops l u).1 p = ⊥ ∧ (boxRun ops l u).2 p = ⊥ := by
  intro ops
  induction ops with
  | nil => intro l u _ h; exact h
  | cons o ops ih =>
    intro l u hops h
    cases o with
    | none => exact ih l u (fun q hq => hops q (List.mem_cons_of_mem _ hq)) h
    | some q =>
      have hq := hops q List.mem_cons_self
      refine ih _ _ (fun q' hq' => hops q' (List.mem_cons_of_mem _ hq')) (fun p hp => ?_)
      have hne : p ≠ q.1 := by omega
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact h p hp

omit [OrderBot Γ] in
/-- Under the invariant, with a box blank beyond `2^n` and blank levels above `n`, the tree
fits in its allocated array. -/
lemma treeFits_of_inv {n : ℕ} {covP covM : A → Finset (ℕ × ℕ)} {bP bM : A → ℕ}
    {acts : Finset A} {K : ℕ} {gk : α → α → A → Γ} {l u : ℕ → α} {s : IState A α Γ}
    (inv : IInv n covP covM bP bM acts K gk l u s)
    (hl : ∀ p, 2 ^ n ≤ p → l p = ⊥) (hu : ∀ p, 2 ^ n ≤ p → u p = ⊥)
    (habove : ∀ k, n < k → ∀ j, s.tree k j = (⊥, ⊥)) : TreeFits n s.tree := by
  intro d hd
  rw [mem_nodeSet] at hd
  by_cases hk : d.1 ≤ n
  · have hj : 2 ^ (n - d.1) ≤ d.2 := by
      by_contra h
      exact hd ⟨hk, by omega⟩
    have a1 : prj1 s.tree d.1 d.2 = ⊥ := by
      rw [inv.treeP d.1 hk d.2]
      exact block_sup_bot hl hk hj
    have a2 : prj2 s.tree d.1 d.2 = ⊥ := by
      rw [inv.treeM d.1 hk d.2]
      exact block_sup_bot hu hk hj
    exact Prod.ext a1 a2
  · exact habove d.1 (by omega) d.2

/-- **Footprint of the index in the memory model**: the shared tree array (`|nodeSet n|`
nodes, two fields each), the cover lists (`B` nodes), the reverse-subscription lists of the
tree nodes, the cells (`heapCells`) of the `2K` action heaps and of the global heap, and the
mark array (`K` cells). -/
noncomputable def iFootprint (n : ℕ) (covPL covML : A → List (ℕ × ℕ))
    (subsP subsM : ℕ × ℕ → List A) (as : List A) (s : IState A α Γ) : ℕ :=
  2 * (nodeSet n).card
    + ((as.map (fun a => (covPL a).length)).sum + (as.map (fun a => (covML a).length)).sum)
    + (∑ d ∈ nodeSet n, (subsP d).length + ∑ d ∈ nodeSet n, (subsM d).length)
    + (as.map (fun a => heapCells (s.hpP a) + heapCells (s.hpM a))).sum
    + heapCells s.gh + as.length

omit [LinearOrder α] [OrderBot α] [DecidableEq A] in
lemma sum_map_lin {β : Type*} (f g : β → ℕ) (c d : ℕ) : ∀ l : List β,
    (l.map (fun a => c * f a + d * g a)).sum = c * (l.map f).sum + d * (l.map g).sum
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, sum_map_lin f g c d l]
    ring

/-- **Space bound**: in every state satisfying the index invariant (after initialisation
and after every update, by `iInit_spec` and `iRun_spec`) the footprint is at most
`2(2^(n+1) - 1) + 5B + 4K`. -/
theorem iFootprint_le (n : ℕ) (covPL covML : A → List (ℕ × ℕ)) (as : List A)
    (gk : α → α → A → Γ) (l u : ℕ → α) (s : IState A α Γ)
    (inv : IInv n (fun a => (covPL a).toFinset) (fun a => (covML a).toFinset)
      (fun a => (covPL a).length) (fun a => (covML a).length) as.toFinset as.length gk l u s) :
    iFootprint n covPL covML (subsOf as covPL) (subsOf as covML) as s
      ≤ 2 * (2 ^ (n + 1) - 1)
        + 5 * ((as.map (fun a => (covPL a).length)).sum
          + (as.map (fun a => (covML a).length)).sum) + 4 * as.length := by
  have t := nodeSet_card_le n
  have sP := subs_cells_le (nodeSet n) covPL as
  have sM := subs_cells_le (nodeSet n) covML as
  have hh : (as.map (fun a => heapCells (s.hpP a) + heapCells (s.hpM a))).sum
      ≤ (as.map (fun a => 3 * (covPL a).length + 3 * (covML a).length)).sum := by
    apply List.sum_le_sum
    intro a _
    have h1 := heapCells_rep (inv.hpP a)
    have h2 := heapCells_rep (inv.hpM a)
    have c1 := List.toFinset_card_le (covPL a)
    have c2 := List.toFinset_card_le (covML a)
    omega
  rw [sum_map_lin] at hh
  have hg := heapCells_rep inv.gh
  have hc := List.toFinset_card_le as
  unfold iFootprint
  omega

end Space

/-! ## The minimiser key: a global min-heap on the regret certificate -/

section MinKey

/-- Keys of the global heap.  The heap is a max-heap; a key is the order dual of the
lexicographic pair (certificate value, action identifier), so the maximal key is the
minimal pair: the global heap is a min-heap on `R_t(a)` with ties broken by the smaller
action identifier. -/
abbrev RKey := WithBot ((Lex (ℝ × ℕ))ᵒᵈ)

/-- The key of action `a` with certificate value `r`. -/
def rkey (r : ℝ) (a : ℕ) : RKey := ((OrderDual.toDual (toLex (r, a)) : (Lex (ℝ × ℕ))ᵒᵈ) : RKey)

/-- The key function of the global heap: `R(a) = φ(U⁻(a)) - φ(L(a))`, where `U⁻(a)` is the
maximum of the upper values over the complement of the support and `L(a)` the maximum of the
lower values over the support. -/
def minKey {α : Type*} (φ : α → ℝ) (um l : α) (a : ℕ) : RKey := rkey (φ um - φ l) a

/-- The maximum of the keys is the key of a minimiser of `R`. -/
theorem sup_rkey (acts : Finset ℕ) (h : acts.Nonempty) (R : ℕ → ℝ) :
    ∃ a ∈ acts, acts.sup (fun b => rkey (R b) b) = rkey (R a) a ∧
      ∀ b ∈ acts, R a < R b ∨ (R a = R b ∧ a ≤ b) := by
  obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup acts h (fun b => rkey (R b) b)
  refine ⟨a, ha, he, fun b hb => ?_⟩
  have h1 := Finset.le_sup (f := fun b => rkey (R b) b) hb
  rw [he] at h1
  simp only [rkey] at h1
  rw [WithBot.coe_le_coe, OrderDual.toDual_le_toDual, Prod.Lex.toLex_le_toLex] at h1
  exact h1

/-- **Minimiser query.**  With the key `minKey φ`, the specification reply for the box
`[l, u]` is the key of an action `a` minimising `R(a) = φ(max_{SM a} u) - φ(max_{SP a} l)`
(smallest identifier among minimisers). -/
theorem boxReply_minimiser {α : Type*} [LinearOrder α] [OrderBot α] (φ : α → ℝ)
    (acts : Finset ℕ) (h : acts.Nonempty) (SP SM : ℕ → Finset ℕ) (l u : ℕ → α) :
    ∃ a ∈ acts, boxReply acts (minKey φ) SP SM l u
        = rkey (φ ((SM a).sup u) - φ ((SP a).sup l)) a ∧
      ∀ b ∈ acts, φ ((SM a).sup u) - φ ((SP a).sup l) < φ ((SM b).sup u) - φ ((SP b).sup l) ∨
        (φ ((SM a).sup u) - φ ((SP a).sup l) = φ ((SM b).sup u) - φ ((SP b).sup l) ∧ a ≤ b) :=
  sup_rkey acts h (fun a => φ ((SM a).sup u) - φ ((SP a).sup l))

end MinKey

/-! ## `thm:charged-dual-cover`: compile, initialise in linear time, run, query, space -/

section Final

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma boxReply_congr {A Γ : Type*} [LinearOrder Γ] [OrderBot Γ] (acts : Finset A)
    (gk : α → α → A → Γ) {SP SM SP' SM' : A → Finset ℕ}
    (h : ∀ a ∈ acts, SP a = SP' a ∧ SM a = SM' a) (l u : ℕ → α) :
    boxReply acts gk SP SM l u = boxReply acts gk SP' SM' l u := by
  unfold boxReply
  exact Finset.sup_congr rfl (fun a ha => by rw [(h a ha).1, (h a ha).2])

lemma specRun_congr {A Γ : Type*} [DecidableEq A] [LinearOrder Γ] [OrderBot Γ]
    (acts : Finset A) (gk : α → α → A → Γ) {SP SM SP' SM' : A → Finset ℕ}
    (h : ∀ a ∈ acts, SP a = SP' a ∧ SM a = SM' a) :
    ∀ (ops : List (Option (ℕ × α × α))) (l u : ℕ → α),
    specRun acts gk SP SM ops l u = specRun acts gk SP' SM' ops l u := by
  intro ops
  induction ops with
  | nil => intro _ _; rfl
  | cons o ops ih =>
    intro l u
    cases o with
    | none =>
      show boxReply acts gk SP SM l u :: _ = boxReply acts gk SP' SM' l u :: _
      rw [boxReply_congr acts gk h, ih]
    | some o => exact ih _ _

/-- **`thm:charged-dual-cover` (with `thm:adaptive-oracle-coupling`), assembled with the
single shared tree, the linear-time initialisation and the global min-heap.**

Circuit `G` with gates `order` (by nondecreasing level, closed under children), terminal
layout positions `pos` in `[0, M)`, supports `supp`, root actions `as` (gates of `order`,
no repetition).  `n = ⌈log₂ M⌉`, `h = n + 1`, `K = |as|`, `R_run = Σ_a r_a`,
`b_a^± = |C_a^±|`, `B = Σ_a (b_a⁺ + b_a⁻)`.  Program: run merging (`RunMerge.runPhase`) and
the dual-cover compiler (`CostModel.compileAll`) give `C_a⁺ = covPlus`, `C_a⁻ = covMinus`;
`iInit` builds ONE shared segment tree holding (lower max, upper max) pairs, the action
heaps (bottom-up, `LiteralK7a.build`) and the global heap keyed by `minKey φ`; then `iRun`
executes any list `ops` of terminal updates (positions below `2^n`) and minimiser queries.

1. covers of every support and complement, and `B ≤ 2h(2R_run + K)`;
2. replies: the `j`-th query returns the specification reply `boxReply` for the terminal box
   at that time, with `SP a = supp a`, `SM a = [0, M) \ supp a`; by `boxReply_minimiser` this
   is the key of an action minimising `R_t(a) = φ(U_t⁻(a)) - φ(L_t(a))`;
3. work: compile + initialisation + run is at most
   `P_G + 4h(2R_run + K) + B + (2^(n+1) - 1) + Σ_a (8b_a⁺ + 1) + Σ_a (8b_a⁻ + 1) + 10K
     + Σ_t updCost_t + Q`, where `updCost_t = 7(h + Σ_{𝒩_t⁺} ⌈log₂(2 + b_a⁺)⌉
     + Σ_{𝒩_t⁻} ⌈log₂(2 + b_a⁻)⌉ + |𝒜_t| ⌈log₂(2 + K)⌉)` (`runSum`) and `Q` is the number
   of queries: this is `eq:dual-cover-work` with explicit constants (`2^(n+1) - 1 < 4M`);
4. `P_G` (`Σ gateCost`, the computed run-merging bound) is at most three times the
   right-hand side of `eq:dual-run-compilation` (`pgTerm`);
5. space: after the run the tree fits in its allocated array and the retained graph plus the
   index footprint is at most `|V| + 2|E| + 8M + 5B + 4K`. -/
theorem charged_dual_cover_literal (G : Dag) (hG : G.WF) (pos : ℕ → ℕ) (M : ℕ) (hM1 : 1 ≤ M)
    (supp : ℕ → Finset ℕ) (order : List ℕ)
    (hsorted : order.Pairwise (fun a b => G.level a ≤ G.level b))
    (hclosed : ∀ g ∈ order, ∀ c ∈ G.children g, c ∈ order)
    (hleaf : ∀ g ∈ order, G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order, G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp)
    (as : List ℕ) (has : ∀ a ∈ as, a ∈ order) (hnd : as.Nodup)
    (φ : α → ℝ) (fl fu : ℕ → α) (hfl : ∀ p, 2 ^ Nat.clog 2 M ≤ p → fl p = ⊥)
    (hfu : ∀ p, 2 ^ Nat.clog 2 M ≤ p → fu p = ⊥)
    (ops : List (Option (ℕ × α × α))) (hops : ∀ q, some q ∈ ops → q.1 < 2 ^ Nat.clog 2 M) :
    let n := Nat.clog 2 M
    let cP := covPlus G pos M order as
    let cM := covMinus G pos M order as
    let B := (as.map (fun a => (cP a).length)).sum + (as.map (fun a => (cM a).length)).sum
    let Rrun := (as.map (fun a => runs (supp a))).sum
    let s0 := iInit n fl fu cP cM (minKey φ) as
    let run := iRun n (subsOf as cP) (subsOf as cM) (minKey φ) ops s0.1
    (∀ a ∈ as, IsDyadicCover ((cP a).map blk).toFinset (supp a) ∧
      IsDyadicCover ((cM a).map blk).toFinset (range M \ supp a)) ∧
    B ≤ 2 * (1 + n) * (2 * Rrun + as.length) ∧
    run.1.2 = specRun as.toFinset (minKey φ) supp (fun a => range M \ supp a) ops fl fu ∧
    (runPhase G pos order (fun _ => [])).2
        + (compileAll n M (as.map (runPhase G pos order (fun _ => [])).1)).2 + s0.2 + run.2
      ≤ (order.map (RunMerge.gateCost G supp)).sum + 4 * (1 + n) * (2 * Rrun + as.length) + B
        + (2 ^ (n + 1) - 1) + (as.map (fun a => 8 * (cP a).length + 1)).sum
        + (as.map (fun a => 8 * (cM a).length + 1)).sum + 10 * as.length
        + runSum n (subsOf as cP) (subsOf as cM) (fun a => (cP a).length)
            (fun a => (cM a).length) as.length ops (prj1 s0.1.tree) (prj2 s0.1.tree)
        + numQ ops ∧
    (order.map (RunMerge.gateCost G supp)).sum ≤ 3 * (order.map (pgTerm G supp)).sum ∧
    TreeFits n run.1.1.tree ∧
    graphCells G + iFootprint n cP cM (subsOf as cP) (subsOf as cM) as run.1.1
      ≤ G.N + 2 * ∑ p ∈ range G.N, (G.children p).length + 8 * M + 5 * B + 4 * as.length := by
  intro n cP cM B Rrun s0 run
  have hM : M ≤ 2 ^ n := Nat.le_pow_clog (by norm_num) M
  obtain ⟨p1, _⟩ := runPhase_spec G pos M supp hG.level_lt order hsorted hclosed hleaf hgate
    (fun _ => [])
  obtain ⟨c1, c2, c3, c4, _⟩ := charged_dual_cover_compile G pos M supp hG.level_lt order
    hsorted hclosed hleaf hgate as has
  have hP : ∀ a ∈ as, cP a
      = (dualCompile n M ((runPhase G pos order (fun _ => [])).1 a)).1.1 :=
    fun a ha => by show covPlus G pos M order as a = _; unfold covPlus; rw [ite_eq_left ha]
  have hMn : ∀ a ∈ as, cM a
      = (dualCompile n M ((runPhase G pos order (fun _ => [])).1 a)).1.2 :=
    fun a ha => by show covMinus G pos M order as a = _; unfold covMinus; rw [ite_eq_left ha]
  have hPout : ∀ a, a ∉ as → cP a = [] :=
    fun a ha => by show covPlus G pos M order as a = _; unfold covPlus; rw [ite_eq_right ha]
  have hMout : ∀ a, a ∉ as → cM a = [] :=
    fun a ha => by show covMinus G pos M order as a = _; unfold covMinus; rw [ite_eq_right ha]
  have hlists : ∀ a ∈ as, _ := fun a ha =>
    dualCompile_lists n M hM _ (p1 a (has a ha)).1
  have hPnd : ∀ a, (cP a).Nodup := by
    intro a
    by_cases ha : a ∈ as
    · rw [hP a ha]; exact (hlists a ha).1
    · rw [hPout a ha]; exact List.nodup_nil
  have hMnd : ∀ a, (cM a).Nodup := by
    intro a
    by_cases ha : a ∈ as
    · rw [hMn a ha]; exact (hlists a ha).2.1
    · rw [hMout a ha]; exact List.nodup_nil
  have hPnodes : ∀ a, ∀ d ∈ cP a, d.1 ≤ n := by
    intro a d hd
    by_cases ha : a ∈ as
    · rw [hP a ha] at hd; exact ((hlists a ha).2.2.1 d hd).1
    · rw [hPout a ha] at hd; simp at hd
  have hMnodes : ∀ a, ∀ d ∈ cM a, d.1 ≤ n := by
    intro a d hd
    by_cases ha : a ∈ as
    · rw [hMn a ha] at hd; exact ((hlists a ha).2.2.2 d hd).1
    · rw [hMout a ha] at hd; simp at hd
  have hcover : ∀ a ∈ as, IsDyadicCover ((cP a).map blk).toFinset (supp a) ∧
      IsDyadicCover ((cM a).map blk).toFinset (range M \ supp a) := by
    intro a ha
    rw [hP a ha, hMn a ha]
    exact c1 a ha
  have hB : B = incidences (compileAll n M (as.map (runPhase G pos order (fun _ => [])).1)).1 := by
    have c2' : (compileAll n M (as.map (runPhase G pos order (fun _ => [])).1)).1
        = as.map (fun a => (dualCompile n M ((runPhase G pos order (fun _ => [])).1 a)).1) := c2
    have e1 : as.map (fun a => (cP a).length) = as.map (fun a =>
        (dualCompile n M ((runPhase G pos order (fun _ => [])).1 a)).1.1.length) :=
      List.map_congr_left (fun a ha => by rw [hP a ha])
    have e2 : as.map (fun a => (cM a).length) = as.map (fun a =>
        (dualCompile n M ((runPhase G pos order (fun _ => [])).1 a)).1.2.length) :=
      List.map_congr_left (fun a ha => by rw [hMn a ha])
    rw [c2', incidences_map]
    show (as.map (fun a => (cP a).length)).sum + (as.map (fun a => (cM a).length)).sum = _
    rw [e1, e2]
  have hsubP : ∀ a, ∀ d ∈ (cP a).toFinset, a ∈ subsOf as cP d := by
    intro a d hd
    have hd' := List.mem_toFinset.1 hd
    have ha : a ∈ as := by
      by_contra hna
      rw [hPout a hna] at hd'
      simp at hd'
    unfold subsOf
    rw [List.mem_filter]
    exact ⟨ha, by simpa using hd'⟩
  have hsubM : ∀ a, ∀ d ∈ (cM a).toFinset, a ∈ subsOf as cM d := by
    intro a d hd
    have hd' := List.mem_toFinset.1 hd
    have ha : a ∈ as := by
      by_contra hna
      rw [hMout a hna] at hd'
      simp at hd'
    unfold subsOf
    rw [List.mem_filter]
    exact ⟨ha, by simpa using hd'⟩
  have hlevP : ∀ a, ∀ d ∈ (cP a).toFinset, d.1 ≤ n :=
    fun a d hd => hPnodes a d (List.mem_toFinset.1 hd)
  have hlevM : ∀ a, ∀ d ∈ (cM a).toFinset, d.1 ≤ n :=
    fun a d hd => hMnodes a d (List.mem_toFinset.1 hd)
  obtain ⟨I1, I2, I3⟩ := iInit_spec n fl fu hfl hfu cP cM (minKey φ) as hnd hPnd hMnd hPout hMout
  obtain ⟨R1, R2, R3⟩ := iRun_spec n (fun a => (cP a).toFinset) (fun a => (cM a).toFinset)
    (subsOf as cP) (subsOf as cM) (fun a => (cP a).length) (fun a => (cM a).length)
    as.toFinset as.length (minKey φ) hsubP hlevP hsubM hlevM ops s0.1 fl fu I1
  have c3' : incidences (compileAll n M (as.map (runPhase G pos order (fun _ => [])).1)).1
      ≤ 2 * (1 + n) * (2 * Rrun + as.length) := c3
  have c4' : (runPhase G pos order (fun _ => [])).2
        + (compileAll n M (as.map (runPhase G pos order (fun _ => [])).1)).2
      ≤ (order.map (RunMerge.gateCost G supp)).sum + 4 * (1 + n) * (2 * Rrun + as.length)
        + incidences (compileAll n M (as.map (runPhase G pos order (fun _ => [])).1)).1 := c4
  refine ⟨hcover, by rw [hB]; exact c3', ?_, ?_, PG_le hG hclosed hleaf hgate, ?_, ?_⟩
  · show (iRun n (subsOf as cP) (subsOf as cM) (minKey φ) ops s0.1).1.2 = _
    rw [R1]
    refine specRun_congr _ _ (fun a ha => ?_) ops fl fu
    have ha' := List.mem_toFinset.1 ha
    exact ⟨biUnion_blk_of_cover (hcover a ha').1, biUnion_blk_of_cover (hcover a ha').2⟩
  · rw [← hB] at c4'
    have I3' : s0.2 ≤ (2 ^ (n + 1) - 1) + (as.map (fun a => 8 * (cP a).length + 1)).sum
        + (as.map (fun a => 8 * (cM a).length + 1)).sum + 10 * as.length := I3
    show _ + _ + s0.2 + (iRun n (subsOf as cP) (subsOf as cM) (minKey φ) ops s0.1).2 ≤ _
    omega
  · have hbl := boxRun_blank (2 ^ n) ops fl fu hops (fun p hp => ⟨hfl p hp, hfu p hp⟩)
    refine treeFits_of_inv R2 (fun p hp => (hbl p hp).1) (fun p hp => (hbl p hp).2) ?_
    intro k hk j
    show (iRun n (subsOf as cP) (subsOf as cM) (minKey φ) ops s0.1).1.1.tree k j = _
    rw [iRun_tree_above n _ _ _ ops s0.1 k j hk]
    exact I2 k hk j
  · have hf := iFootprint_le n cP cM as (minKey φ) _ _ _ R2
    have hg := graphCells_le hG
    have hn : 2 ^ (n + 1) - 1 < 4 * M := segTree_nodes_lt M hM1
    show graphCells G + iFootprint n cP cM (subsOf as cP) (subsOf as cM) as
      (iRun n (subsOf as cP) (subsOf as cM) (minKey φ) ops s0.1).1.1 ≤ _
    omega

/-- **The dual-cover index as an `OracleImpl` exposing the exact minimiser oracle.**  Started
from the costed initialisation `iInit`, the index implementation `dualImpl` (one terminal
update per observation, reply = root of the global min-heap read through `out`) has, on
every history, the answer of the specification oracle that recomputes
`min_a R_t(a)` (as `boxReply` with `minKey φ`) from the terminal box with `SP a = supp a`
and `SM a = [0, M) \ supp a`.  By `Representation.exact_coupling`, any implementation
exposing this oracle (in particular the specification itself, or a full-DAG evaluation that
returns the same reply) induces identical histories, replies and stopping times. -/
theorem dual_cover_oracle {Z X St Rp : Type*} (G : Dag) (hG : G.WF) (pos : ℕ → ℕ) (M : ℕ)
    (supp : ℕ → Finset ℕ) (order : List ℕ)
    (hsorted : order.Pairwise (fun a b => G.level a ≤ G.level b))
    (hclosed : ∀ g ∈ order, ∀ c ∈ G.children g, c ∈ order)
    (hleaf : ∀ g ∈ order, G.children g = [] → supp g = {pos g} ∧ pos g < M)
    (hgate : ∀ g ∈ order, G.children g ≠ [] → supp g = (G.children g).toFinset.biUnion supp)
    (as : List ℕ) (has : ∀ a ∈ as, a ∈ order) (hnd : as.Nodup)
    (φ : α → ℝ) (fl fu : ℕ → α) (hfl : ∀ p, 2 ^ Nat.clog 2 M ≤ p → fl p = ⊥)
    (hfu : ∀ p, 2 ^ Nat.clog 2 M ≤ p → fu p = ⊥) (out : RKey → Rp)
    (st0 : St) (stp : St → Z × X → St) (iv : St → Z → α × α) (lpos : Z → ℕ)
    (h : List (Z × X)) :
    (dualImpl (Nat.clog 2 M) (subsOf as (covPlus G pos M order as))
        (subsOf as (covMinus G pos M order as)) (minKey φ) out
        (iInit (Nat.clog 2 M) fl fu (covPlus G pos M order as) (covMinus G pos M order as)
          (minKey φ) as).1 st0 stp iv lpos).answer h
      = (specImpl as.toFinset (minKey φ) out supp (fun a => range M \ supp a) fl fu st0 stp iv
          lpos).answer h := by
  have hM : M ≤ 2 ^ Nat.clog 2 M := Nat.le_pow_clog (by norm_num) M
  obtain ⟨p1, _⟩ := runPhase_spec G pos M supp hG.level_lt order hsorted hclosed hleaf hgate
    (fun _ => [])
  obtain ⟨c1, _, _, _, _⟩ := charged_dual_cover_compile G pos M supp hG.level_lt order
    hsorted hclosed hleaf hgate as has
  have hP : ∀ a ∈ as, covPlus G pos M order as a
      = (dualCompile (Nat.clog 2 M) M ((runPhase G pos order (fun _ => [])).1 a)).1.1 :=
    fun a ha => by unfold covPlus; rw [ite_eq_left ha]
  have hMn : ∀ a ∈ as, covMinus G pos M order as a
      = (dualCompile (Nat.clog 2 M) M ((runPhase G pos order (fun _ => [])).1 a)).1.2 :=
    fun a ha => by unfold covMinus; rw [ite_eq_left ha]
  have hPout : ∀ a, a ∉ as → covPlus G pos M order as a = [] :=
    fun a ha => by unfold covPlus; rw [ite_eq_right ha]
  have hMout : ∀ a, a ∉ as → covMinus G pos M order as a = [] :=
    fun a ha => by unfold covMinus; rw [ite_eq_right ha]
  have hlists : ∀ a ∈ as, _ := fun a ha =>
    dualCompile_lists (Nat.clog 2 M) M hM _ (p1 a (has a ha)).1
  have hPnd : ∀ a, (covPlus G pos M order as a).Nodup := by
    intro a
    by_cases ha : a ∈ as
    · rw [hP a ha]; exact (hlists a ha).1
    · rw [hPout a ha]; exact List.nodup_nil
  have hMnd : ∀ a, (covMinus G pos M order as a).Nodup := by
    intro a
    by_cases ha : a ∈ as
    · rw [hMn a ha]; exact (hlists a ha).2.1
    · rw [hMout a ha]; exact List.nodup_nil
  have hlevP : ∀ a, ∀ d ∈ (covPlus G pos M order as a).toFinset, d.1 ≤ Nat.clog 2 M := by
    intro a d hd
    have hd' := List.mem_toFinset.1 hd
    by_cases ha : a ∈ as
    · rw [hP a ha] at hd'; exact ((hlists a ha).2.2.1 d hd').1
    · rw [hPout a ha] at hd'; simp at hd'
  have hlevM : ∀ a, ∀ d ∈ (covMinus G pos M order as a).toFinset, d.1 ≤ Nat.clog 2 M := by
    intro a d hd
    have hd' := List.mem_toFinset.1 hd
    by_cases ha : a ∈ as
    · rw [hMn a ha] at hd'; exact ((hlists a ha).2.2.2 d hd').1
    · rw [hMout a ha] at hd'; simp at hd'
  have hsub : ∀ (cL : ℕ → List (ℕ × ℕ)), (∀ a, a ∉ as → cL a = []) →
      ∀ a, ∀ d ∈ (cL a).toFinset, a ∈ subsOf as cL d := by
    intro cL hout a d hd
    have hd' := List.mem_toFinset.1 hd
    have ha : a ∈ as := by
      by_contra hna
      rw [hout a hna] at hd'
      simp at hd'
    unfold subsOf
    rw [List.mem_filter]
    exact ⟨ha, by simpa using hd'⟩
  obtain ⟨I1, _, _⟩ := iInit_spec (Nat.clog 2 M) fl fu hfl hfu (covPlus G pos M order as)
    (covMinus G pos M order as) (minKey φ) as hnd hPnd hMnd hPout hMout
  rw [dual_answer_eq (Nat.clog 2 M) _ _ _ _ _ _ _ as.length (minKey φ) out
    (hsub _ hPout) hlevP (hsub _ hMout) hlevM fl fu _ I1 st0 stp iv lpos h]
  show out (boxReply _ _ _ _ _ _) = out (boxReply _ _ _ _ _ _)
  congr 1
  refine boxReply_congr _ _ (fun a ha => ?_) _ _
  have ha' := List.mem_toFinset.1 ha
  have hc := c1 a ha'
  rw [← hP a ha', ← hMn a ha'] at hc
  exact ⟨biUnion_blk_of_cover hc.1, biUnion_blk_of_cover hc.2⟩

end Final

end LiteralK7
end JointRootCert
