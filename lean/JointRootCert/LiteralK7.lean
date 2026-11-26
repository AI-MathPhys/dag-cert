/-
PLACEHOLDER HEADER
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

end LiteralK7
end JointRootCert
