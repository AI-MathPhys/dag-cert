/-
Joint Root Certification: representation coupling and charged maintenance bounds.

Manuscript: Part III, section "Efficient Algorithms and Certified Numerical Methods"
(`app:group-compute`), subsection `app:representation`.  Results covered:

* `thm:charged-dual-cover` / `thm:adaptive-oracle-coupling`
  (Exact coupling and charged maintenance): the trajectory coupling and the incidence
  bound `B ≤ 2h(2R_run + K)`.  The RAM work and space bounds are not formalized.
* `prop:representation-coupling` (Trajectory Coupling Across Circuit Representations).
* `prop:representation-cost` (Unified Full-Cost Representation Comparison): the delivery
  accounting and the asymptotic consequence, with per-operation charges as hypotheses.
* `thm:coded-main` / `thm:coded-covers` (Every-layout dyadic cover lower bound): the
  parity-grid construction and the every-layout `Ω(r^3)` incidence lower bound (Steps 1-2).
  The probabilistic `O(r^2 log^2 r)` upper bound (Step 3) is not formalized, except for the
  deterministic selection inequality.
* `prop:unrestricted-compiler` (Equivalence Under Unrestricted Circuit Retention): the
  semantic part only.
-/
import JointRootCert.ActiveBounds

namespace JointRootCert
namespace Representation

open Finset

/-! ## Runs of a set of positions

A terminal ordering (layout) places the terminals at positions `0, …, M-1`.  A support is
then a finite set `T` of positions, and its maximal contiguous runs are counted by their
right ends. -/

/-- Right ends of the maximal contiguous runs of `T`. -/
def runEnds (T : Finset ℕ) : Finset ℕ := T.filter (fun x => x + 1 ∉ T)

/-- Left ends of the maximal contiguous runs of `T`. -/
def runStarts (T : Finset ℕ) : Finset ℕ := T.filter (fun x => x = 0 ∨ x - 1 ∉ T)

/-- The number `r` of maximal contiguous runs of `T` (the run count `r_a` of a root support
in the proof of `thm:charged-dual-cover`). -/
def runs (T : Finset ℕ) : ℕ := (runEnds T).card

/-- Runs have as many left ends as right ends. -/
lemma card_runStarts (T : Finset ℕ) : (runStarts T).card = runs T := by
  have h1 := card_filter_add_card_filter_not (s := T) (fun x => x + 1 ∈ T)
  have h2 := card_filter_add_card_filter_not (s := T) (fun x => x ≠ 0 ∧ x - 1 ∈ T)
  have h3 : (T.filter (fun x => x ≠ 0 ∧ x - 1 ∈ T))
      = (T.filter (fun x => x + 1 ∈ T)).image (· + 1) := by
    ext y
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hy, hy0, hy1⟩
      have hpos : 1 ≤ y := Nat.pos_of_ne_zero hy0
      exact ⟨y - 1, ⟨hy1, by rwa [Nat.sub_add_cancel hpos]⟩, Nat.sub_add_cancel hpos⟩
    · rintro ⟨x, ⟨hx, hx1⟩, rfl⟩
      exact ⟨hx1, Nat.succ_ne_zero x, by simpa using hx⟩
  have h4 : ((T.filter (fun x => x + 1 ∈ T)).image (· + 1)).card
      = (T.filter (fun x => x + 1 ∈ T)).card :=
    card_image_of_injective _ (fun a b h => by simpa using h)
  have h5 : runStarts T = T.filter (fun x => ¬ (x ≠ 0 ∧ x - 1 ∈ T)) := by
    unfold runStarts
    apply filter_congr
    intro x _
    tauto
  rw [h3, h4] at h2
  unfold runs runEnds
  rw [h5]
  omega

/-- Number of `0 ↔ 1` transitions of the indicator of `T` along positions `0, …, N-1`. -/
def transitions (T : Finset ℕ) (N : ℕ) : ℕ :=
  ((range (N - 1)).filter (fun s => ¬ (s ∈ T ↔ s + 1 ∈ T))).card

/-- A binary indicator sequence has at most twice as many transitions as runs of ones
(Step 2 of the proof of `thm:coded-covers`). -/
lemma transitions_le (T : Finset ℕ) (N : ℕ) : transitions T N ≤ 2 * runs T := by
  have hsub : (range (N - 1)).filter (fun s => ¬ (s ∈ T ↔ s + 1 ∈ T))
      ⊆ runEnds T ∪ (runStarts T).image (fun x => x - 1) := by
    intro s hs
    rw [mem_filter] at hs
    rw [mem_union, mem_image]
    by_cases h : s ∈ T
    · left
      exact mem_filter.2 ⟨h, fun h' => hs.2 ⟨fun _ => h', fun _ => h⟩⟩
    · right
      refine ⟨s + 1, mem_filter.2 ⟨?_, Or.inr (by simpa using h)⟩, by simp⟩
      by_contra h'
      exact hs.2 ⟨fun a => absurd a h, fun a => absurd a h'⟩
  calc transitions T N
      ≤ (runEnds T ∪ (runStarts T).image (fun x => x - 1)).card := card_le_card hsub
    _ ≤ (runEnds T).card + ((runStarts T).image (fun x => x - 1)).card := card_union_le _ _
    _ ≤ runs T + runs T := add_le_add le_rfl (card_image_le.trans (card_runStarts T).le)
    _ = 2 * runs T := by ring

/-- The complement of a support with `r` runs has at most `r + 1` runs
(proof of `thm:charged-dual-cover`). -/
lemma runs_compl_le (T : Finset ℕ) (M : ℕ) : runs (range M \ T) ≤ runs T + 1 := by
  have hsub : runEnds (range M \ T)
      ⊆ insert (M - 1) ((runStarts T).image (fun x => x - 1)) := by
    intro x hx
    simp only [runEnds, mem_filter, mem_sdiff, mem_range, not_and, not_not] at hx
    obtain ⟨⟨hxM, hxT⟩, h⟩ := hx
    rw [mem_insert, mem_image]
    by_cases h1 : x + 1 < M
    · right
      exact ⟨x + 1, mem_filter.2 ⟨h h1, Or.inr (by simpa using hxT)⟩, by simp⟩
    · left
      omega
  have h1 := card_le_card hsub
  have h2 := card_insert_le (M - 1) ((runStarts T).image (fun x => x - 1))
  have h3 := card_image_le (s := runStarts T) (f := fun x => x - 1)
  have h4 := card_runStarts T
  unfold runs at *
  omega

/-! ## Dyadic blocks and dyadic covers -/

/-- The dyadic block of level `k` and index `j`: positions `[j 2^k, (j+1) 2^k)`.  These are
the nodes of a binary segment tree over the positions. -/
def dyadicBlock (k j : ℕ) : Finset ℕ := Ico (j * 2 ^ k) ((j + 1) * 2 ^ k)

/-- A dyadic block contained in `[0, 2^n)` is a node of the segment tree with `2^n`
leaves: its level is at most `n` and its index is below `2^(n-k)`. -/
lemma dyadicBlock_node {n k j : ℕ} (h : dyadicBlock k j ⊆ range (2 ^ n)) :
    k ≤ n ∧ j < 2 ^ (n - k) := by
  have hpos : 0 < 2 ^ k := by positivity
  have hmem : (j + 1) * 2 ^ k - 1 ∈ dyadicBlock k j := by
    have : (j + 1) * 2 ^ k = j * 2 ^ k + 2 ^ k := by ring
    simp only [dyadicBlock, mem_Ico]
    omega
  have hlt := mem_range.1 (h hmem)
  have hle : (j + 1) * 2 ^ k ≤ 2 ^ n := by omega
  have hk : k ≤ n := by
    have h1 : 2 ^ k ≤ (j + 1) * 2 ^ k := Nat.le_mul_of_pos_left _ (Nat.succ_pos j)
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (h1.trans hle)
  refine ⟨hk, ?_⟩
  have h2 : (2 : ℕ) ^ n = 2 ^ (n - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [h2] at hle
  exact Nat.lt_of_succ_le (Nat.le_of_mul_le_mul_right hle hpos)

/-- `C` is a dyadic cover of the position set `T`: a family of pairwise disjoint dyadic
blocks with union `T`.  This is the list of dyadic intervals materialized for one root
support (or one complement) under a fixed layout; `C.card` is its number of root-to-block
incidences. -/
structure IsDyadicCover (C : Finset (Finset ℕ)) (T : Finset ℕ) : Prop where
  isBlock : ∀ B ∈ C, ∃ k j, B = dyadicBlock k j
  pairwiseDisjoint : ∀ B ∈ C, ∀ B' ∈ C, B ≠ B' → Disjoint B B'
  biUnion_eq : C.biUnion id = T

namespace IsDyadicCover

lemma subset {C : Finset (Finset ℕ)} {T : Finset ℕ} (h : IsDyadicCover C T)
    {B : Finset ℕ} (hB : B ∈ C) : B ⊆ T := by
  rw [← h.biUnion_eq]
  exact subset_biUnion_of_mem id hB

lemma empty : IsDyadicCover ∅ ∅ where
  isBlock := by simp
  pairwiseDisjoint := by simp
  biUnion_eq := by simp

lemma single (k j : ℕ) : IsDyadicCover {dyadicBlock k j} (dyadicBlock k j) where
  isBlock := fun B hB => ⟨k, j, mem_singleton.1 hB⟩
  pairwiseDisjoint := by
    intro B hB B' hB' hne
    rw [mem_singleton] at hB hB'
    exact absurd (hB.trans hB'.symm) hne
  biUnion_eq := by simp

lemma append {C C' : Finset (Finset ℕ)} {T T' : Finset ℕ} (h : IsDyadicCover C T)
    (h' : IsDyadicCover C' T') (hd : Disjoint T T') :
    IsDyadicCover (C ∪ C') (T ∪ T') where
  isBlock := fun B hB => (mem_union.1 hB).elim (h.isBlock B) (h'.isBlock B)
  pairwiseDisjoint := by
    intro B hB B' hB' hne
    rcases mem_union.1 hB with h1 | h1 <;> rcases mem_union.1 hB' with h2 | h2
    · exact h.pairwiseDisjoint B h1 B' h2 hne
    · exact hd.mono (h.subset h1) (h'.subset h2)
    · exact hd.symm.mono (h'.subset h1) (h.subset h2)
    · exact h'.pairwiseDisjoint B h1 B' h2 hne
  biUnion_eq := by rw [union_biUnion, h.biUnion_eq, h'.biUnion_eq]

end IsDyadicCover

lemma dyadicBlock_eq_Ico {k c : ℕ} (h : 2 ^ k ∣ c) :
    dyadicBlock k (c / 2 ^ k) = Ico c (c + 2 ^ k) := by
  unfold dyadicBlock
  rw [add_mul, Nat.div_mul_cancel h, one_mul]

/-- A prefix `[c, c + b)` of an aligned window of length `2^n` is a union of at most
`n + 1` dyadic blocks. -/
lemma exists_cover_prefix (n : ℕ) : ∀ c b, 2 ^ n ∣ c → b ≤ 2 ^ n →
    ∃ C, IsDyadicCover C (Ico c (c + b)) ∧ C.card ≤ n + 1 := by
  induction n with
  | zero =>
    intro c b hc hb
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0
      exact ⟨∅, by simpa using IsDyadicCover.empty, by simp⟩
    · have hb1 : b = 1 := by simp at hb; omega
      subst hb1
      refine ⟨{dyadicBlock 0 c}, ?_, by simp⟩
      have := IsDyadicCover.single 0 c
      simpa [dyadicBlock] using this
  | succ n ih =>
    intro c b hc hb
    have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hc' : 2 ^ n ∣ c := (Dvd.intro_left 2 h2.symm).trans hc
    by_cases hbn : b ≤ 2 ^ n
    · obtain ⟨C, hC, hcard⟩ := ih c b hc' hbn
      exact ⟨C, hC, by omega⟩
    · obtain ⟨C, hC, hcard⟩ := ih (c + 2 ^ n) (b - 2 ^ n) (Dvd.dvd.add hc' dvd_rfl) (by omega)
      refine ⟨{dyadicBlock n (c / 2 ^ n)} ∪ C, ?_, ?_⟩
      · have hd : Disjoint (dyadicBlock n (c / 2 ^ n))
            (Ico (c + 2 ^ n) (c + 2 ^ n + (b - 2 ^ n))) := by
          rw [dyadicBlock_eq_Ico hc']
          exact Ico_disjoint_Ico_consecutive _ _ _
        have := (IsDyadicCover.single n (c / 2 ^ n)).append hC hd
        rw [dyadicBlock_eq_Ico hc', Ico_union_Ico_eq_Ico (by omega) (by omega)] at this
        have he : c + 2 ^ n + (b - 2 ^ n) = c + b := by omega
        rw [dyadicBlock_eq_Ico hc']
        rwa [he] at this
      · have := card_union_le {dyadicBlock n (c / 2 ^ n)} C
        simp only [card_singleton] at this
        omega

/-- A suffix `[c - b, c)` of an aligned window of length `2^n` is a union of at most
`n + 1` dyadic blocks. -/
lemma exists_cover_suffix (n : ℕ) : ∀ c b, 2 ^ n ∣ c → b ≤ 2 ^ n → b ≤ c →
    ∃ C, IsDyadicCover C (Ico (c - b) c) ∧ C.card ≤ n + 1 := by
  induction n with
  | zero =>
    intro c b hc hb hbc
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0
      exact ⟨∅, by simpa using IsDyadicCover.empty, by simp⟩
    · have hb1 : b = 1 := by simp at hb; omega
      subst hb1
      refine ⟨{dyadicBlock 0 (c - 1)}, ?_, by simp⟩
      have := IsDyadicCover.single 0 (c - 1)
      have he : c - 1 + 1 = c := by omega
      simpa [dyadicBlock, he] using this
  | succ n ih =>
    intro c b hc hb hbc
    have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hc' : 2 ^ n ∣ c := (Dvd.intro_left 2 h2.symm).trans hc
    by_cases hbn : b ≤ 2 ^ n
    · obtain ⟨C, hC, hcard⟩ := ih c b hc' hbn hbc
      exact ⟨C, hC, by omega⟩
    · have hcn : 2 ^ n ≤ c := by omega
      have hc'' : 2 ^ n ∣ c - 2 ^ n := Nat.dvd_sub hc' dvd_rfl
      obtain ⟨C, hC, hcard⟩ := ih (c - 2 ^ n) (b - 2 ^ n) hc'' (by omega) (by omega)
      have hblk : dyadicBlock n ((c - 2 ^ n) / 2 ^ n) = Ico (c - 2 ^ n) c := by
        rw [dyadicBlock_eq_Ico hc'']
        congr 1
        omega
      refine ⟨C ∪ {dyadicBlock n ((c - 2 ^ n) / 2 ^ n)}, ?_, ?_⟩
      · have hd : Disjoint (Ico (c - 2 ^ n - (b - 2 ^ n)) (c - 2 ^ n))
            (dyadicBlock n ((c - 2 ^ n) / 2 ^ n)) := by
          rw [hblk]
          exact Ico_disjoint_Ico_consecutive _ _ _
        have := hC.append (IsDyadicCover.single n ((c - 2 ^ n) / 2 ^ n)) hd
        rw [hblk, Ico_union_Ico_eq_Ico (by omega) (by omega)] at this
        have he : c - 2 ^ n - (b - 2 ^ n) = c - b := by omega
        rw [hblk]
        rwa [he] at this
      · have := card_union_le C {dyadicBlock n ((c - 2 ^ n) / 2 ^ n)}
        simp only [card_singleton] at this
        omega

/-- Every interval inside an aligned window of length `2^n` is a union of at most `2n + 1`
dyadic blocks. -/
lemma exists_cover_window (n : ℕ) : ∀ c a b, 2 ^ n ∣ c → a ≤ b → b ≤ 2 ^ n →
    ∃ C, IsDyadicCover C (Ico (c + a) (c + b)) ∧ C.card ≤ 2 * n + 1 := by
  induction n with
  | zero =>
    intro c a b hc hab hb
    by_cases h : a = b
    · subst h
      exact ⟨∅, by simpa using IsDyadicCover.empty, by simp⟩
    · have hb1 : b = 1 := by simp at hb; omega
      have ha0 : a = 0 := by omega
      subst hb1 ha0
      obtain ⟨C, hC, hcard⟩ := exists_cover_prefix 0 c 1 hc (by simp)
      exact ⟨C, by simpa using hC, by simpa using hcard⟩
  | succ n ih =>
    intro c a b hc hab hb
    have h2 : (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n := by ring
    have hc' : 2 ^ n ∣ c := (Dvd.intro_left 2 h2.symm).trans hc
    by_cases hbn : b ≤ 2 ^ n
    · obtain ⟨C, hC, hcard⟩ := ih c a b hc' hab hbn
      exact ⟨C, hC, by omega⟩
    by_cases han : 2 ^ n ≤ a
    · obtain ⟨C, hC, hcard⟩ :=
        ih (c + 2 ^ n) (a - 2 ^ n) (b - 2 ^ n) (Dvd.dvd.add hc' dvd_rfl) (by omega) (by omega)
      have h1 : c + 2 ^ n + (a - 2 ^ n) = c + a := by omega
      have h3 : c + 2 ^ n + (b - 2 ^ n) = c + b := by omega
      rw [h1, h3] at hC
      exact ⟨C, hC, by omega⟩
    · have hcn : 2 ^ n ∣ c + 2 ^ n := Dvd.dvd.add hc' dvd_rfl
      obtain ⟨C₁, hC₁, hcard₁⟩ :=
        exists_cover_suffix n (c + 2 ^ n) (2 ^ n - a) hcn (by omega) (by omega)
      obtain ⟨C₂, hC₂, hcard₂⟩ :=
        exists_cover_prefix n (c + 2 ^ n) (b - 2 ^ n) hcn (by omega)
      have h1 : c + 2 ^ n - (2 ^ n - a) = c + a := by omega
      have h3 : c + 2 ^ n + (b - 2 ^ n) = c + b := by omega
      rw [h1] at hC₁
      rw [h3] at hC₂
      refine ⟨C₁ ∪ C₂, ?_, ?_⟩
      · have := hC₁.append hC₂ (Ico_disjoint_Ico_consecutive _ _ _)
        rwa [Ico_union_Ico_eq_Ico (by omega) (by omega)] at this
      · have := card_union_le C₁ C₂
        omega

/-- **Dyadic decomposition of a contiguous interval.**  Every interval `[a, b)` of
positions inside `[0, 2^n)` is a disjoint union of at most `2n + 1 ≤ 2h` dyadic blocks,
where `h = 1 + n` (proof of `thm:charged-dual-cover`: "each contiguous interval decomposes
into at most `2h` canonical dyadic blocks"). -/
theorem exists_cover_Ico (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ 2 ^ n) :
    ∃ C, IsDyadicCover C (Ico a b) ∧ C.card ≤ 2 * n + 1 := by
  simpa using exists_cover_window n 0 a b (dvd_zero _) hab hb

/-- **Dyadic cover of a support with `r` runs.**  A set of positions inside `[0, 2^n)`
with `r` maximal runs has a dyadic cover with at most `r (2n + 1)` blocks. -/
theorem exists_dyadicCover (n : ℕ) (T : Finset ℕ) (hT : T ⊆ range (2 ^ n)) :
    ∃ C, IsDyadicCover C T ∧ C.card ≤ runs T * (2 * n + 1) := by
  induction T using Finset.strongInduction with
  | H T ih =>
    rcases T.eq_empty_or_nonempty with rfl | hne
    · exact ⟨∅, IsDyadicCover.empty, by simp⟩
    set m := T.max' hne with hm
    have hmT : m ∈ T := T.max'_mem hne
    have hex : ∃ a, Ico a (m + 1) ⊆ T := ⟨m, by
      intro x hx
      rw [mem_Ico] at hx
      have : x = m := by omega
      rwa [this]⟩
    set a := Nat.find hex with ha
    have haT : Ico a (m + 1) ⊆ T := Nat.find_spec hex
    have ham : a ≤ m := Nat.find_min' hex (by
      intro x hx
      rw [mem_Ico] at hx
      have : x = m := by omega
      rwa [this])
    set T' := T.filter (fun x => x < a) with hT'
    have hT'sub : T' ⊆ T := filter_subset _ _
    have hss : T' ⊂ T := by
      refine ⟨hT'sub, fun h => ?_⟩
      have := (mem_filter.1 (h hmT)).2
      omega
    have hunion : T' ∪ Ico a (m + 1) = T := by
      ext x
      simp only [mem_union, hT', mem_filter, mem_Ico]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact haT (mem_Ico.2 h)
      · intro hx
        have := T.le_max' x hx
        by_cases hxa : x < a
        · exact Or.inl ⟨hx, hxa⟩
        · exact Or.inr ⟨by omega, by omega⟩
    have hdisj : Disjoint T' (Ico a (m + 1)) := by
      rw [disjoint_left]
      intro x hx hx'
      have := (mem_filter.1 hx).2
      have := (mem_Ico.1 hx').1
      omega
    have hruns : runs T' + 1 ≤ runs T := by
      have hmnot : m ∉ runEnds T' := by
        intro h
        have := (mem_filter.1 ((mem_filter.1 h).1)).2
        omega
      have hsub : insert m (runEnds T') ⊆ runEnds T := by
        intro x hx
        rw [mem_insert] at hx
        rcases hx with rfl | hx
        · refine mem_filter.2 ⟨hmT, fun h => ?_⟩
          have := T.le_max' _ h
          omega
        · obtain ⟨hxT', hx1⟩ := mem_filter.1 hx
          obtain ⟨hxT, hxa⟩ := mem_filter.1 hxT'
          refine mem_filter.2 ⟨hxT, fun h => ?_⟩
          by_cases hlt : x + 1 < a
          · exact hx1 (mem_filter.2 ⟨h, hlt⟩)
          · have hxa' : x + 1 = a := by omega
            have hbad : Ico x (m + 1) ⊆ T := by
              intro y hy
              rw [mem_Ico] at hy
              by_cases hyx : y = x
              · rwa [hyx]
              · exact haT (mem_Ico.2 ⟨by omega, hy.2⟩)
            have := Nat.find_min hex (m := x) (by omega)
            exact this hbad
      have := card_le_card hsub
      rw [card_insert_of_notMem hmnot] at this
      exact this
    obtain ⟨C', hC', hcard'⟩ := ih T' hss (hT'sub.trans hT)
    have hm1 : m + 1 ≤ 2 ^ n := by
      have := mem_range.1 (hT hmT)
      omega
    obtain ⟨C'', hC'', hcard''⟩ := exists_cover_Ico n a (m + 1) (by omega) hm1
    refine ⟨C' ∪ C'', ?_, ?_⟩
    · have := hC'.append hC'' hdisj
      rwa [hunion] at this
    · have h1 := card_union_le C' C''
      have h2 : (runs T' + 1) * (2 * n + 1) ≤ runs T * (2 * n + 1) :=
        Nat.mul_le_mul_right _ hruns
      have h3 : (runs T' + 1) * (2 * n + 1) = runs T' * (2 * n + 1) + (2 * n + 1) := by ring
      omega

/-- **Blocks are at least runs.**  Every dyadic cover of `T` has at least as many blocks
as `T` has maximal runs, because each block is a contiguous sub-interval of `T`
(Step 2 of the proof of `thm:coded-covers`).  Disjointness of the blocks is not used. -/
theorem runs_le_card_of_cover {C : Finset (Finset ℕ)} {T : Finset ℕ}
    (h : IsDyadicCover C T) : runs T ≤ C.card := by
  have hsub : runEnds T ⊆ C.image (fun B => B.sup id) := by
    intro x hx
    obtain ⟨hxT, hx1⟩ := mem_filter.1 hx
    rw [← h.biUnion_eq, mem_biUnion] at hxT
    obtain ⟨B, hB, hxB⟩ := hxT
    refine mem_image.2 ⟨B, hB, ?_⟩
    apply le_antisymm
    · apply Finset.sup_le
      intro y hy
      by_contra hlt
      obtain ⟨k, j, rfl⟩ := h.isBlock B hB
      have hxB' : x ∈ dyadicBlock k j := hxB
      simp only [dyadicBlock, mem_Ico, id] at hxB' hy hlt
      have : x + 1 ∈ dyadicBlock k j := by
        simp only [dyadicBlock, mem_Ico]
        omega
      exact hx1 (h.subset hB this)
    · exact Finset.le_sup (f := id) hxB
  exact (card_le_card hsub).trans card_image_le

/-! ## Layouts and the charged dual-cover incidence bound -/

/-- Positions occupied by the support `S` under the layout (terminal ordering) `π`. -/
def layoutPos {Z : Type*} [DecidableEq Z] {M : ℕ} (π : Z ≃ Fin M) (S : Finset Z) :
    Finset ℕ := S.image (fun z => (π z : ℕ))

lemma mem_layoutPos {Z : Type*} [DecidableEq Z] {M : ℕ} (π : Z ≃ Fin M) (S : Finset Z)
    (s : ℕ) : s ∈ layoutPos π S ↔ ∃ h : s < M, π.symm ⟨s, h⟩ ∈ S := by
  simp only [layoutPos, mem_image]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(π z).2, by simpa using hz⟩
  · rintro ⟨h, hs⟩
    exact ⟨_, hs, by simp⟩

lemma layoutPos_subset {Z : Type*} [DecidableEq Z] {M : ℕ} (π : Z ≃ Fin M) (S : Finset Z) :
    layoutPos π S ⊆ range M := by
  intro s hs
  obtain ⟨h, -⟩ := (mem_layoutPos π S s).1 hs
  exact mem_range.2 h

lemma layoutPos_compl {Z : Type*} [Fintype Z] [DecidableEq Z] {M : ℕ} (π : Z ≃ Fin M)
    (S : Finset Z) : layoutPos π Sᶜ = range M \ layoutPos π S := by
  ext s
  rw [mem_sdiff, mem_range, mem_layoutPos, mem_layoutPos]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, fun ⟨_, hs'⟩ => (mem_compl.1 hs) hs'⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, mem_compl.2 (fun hs' => hs ⟨h, hs'⟩)⟩

/-- **Charged dual covers: incidence bound** (`thm:charged-dual-cover`).  For `K` root
actions with supports `S a` over `M` terminals, under any layout `π`, there are dyadic
covers `C⁺ a` of each support and `C⁻ a` of each complement whose total number of
incidences `B` satisfies `B ≤ 2 h (2 R_run + K)`, with `h = 1 + ⌈log₂ M⌉` and
`R_run = Σ_a r_a` the total run count.  All blocks are nodes of the segment tree with
`2^⌈log₂ M⌉` leaves by `dyadicBlock_node`. -/
theorem dualCover_incidence_bound {Z A : Type*} [Fintype Z] [DecidableEq Z] [Fintype A]
    {M : ℕ} (π : Z ≃ Fin M) (S : A → Finset Z) :
    ∃ Cp Cm : A → Finset (Finset ℕ),
      (∀ a, IsDyadicCover (Cp a) (layoutPos π (S a))) ∧
      (∀ a, IsDyadicCover (Cm a) (layoutPos π (S a)ᶜ)) ∧
      ∑ a, ((Cp a).card + (Cm a).card)
        ≤ 2 * (1 + Nat.clog 2 M) * (2 * ∑ a, runs (layoutPos π (S a)) + Fintype.card A) := by
  set n := Nat.clog 2 M with hn
  have hM : range M ⊆ range (2 ^ n) :=
    range_subset_range.2 (Nat.le_pow_clog (by norm_num) M)
  have hp : ∀ a, ∃ C, IsDyadicCover C (layoutPos π (S a)) ∧
      C.card ≤ runs (layoutPos π (S a)) * (2 * n + 1) := fun a =>
    exists_dyadicCover n _ ((layoutPos_subset π (S a)).trans hM)
  have hm : ∀ a, ∃ C, IsDyadicCover C (layoutPos π (S a)ᶜ) ∧
      C.card ≤ (runs (layoutPos π (S a)) + 1) * (2 * n + 1) := fun a => by
    obtain ⟨C, hC, hcard⟩ :=
      exists_dyadicCover n _ ((layoutPos_subset π (S a)ᶜ).trans hM)
    refine ⟨C, hC, hcard.trans (Nat.mul_le_mul_right _ ?_)⟩
    rw [layoutPos_compl]
    exact runs_compl_le _ _
  choose Cp hCp hcp using hp
  choose Cm hCm hcm using hm
  refine ⟨Cp, Cm, hCp, hCm, ?_⟩
  calc ∑ a, ((Cp a).card + (Cm a).card)
      ≤ ∑ a, 2 * (1 + n) * (2 * runs (layoutPos π (S a)) + 1) := by
        apply sum_le_sum
        intro a _
        have h1 := hcp a
        have h2 := hcm a
        nlinarith [Nat.zero_le (runs (layoutPos π (S a))), Nat.zero_le n]
    _ = 2 * (1 + n) * (2 * ∑ a, runs (layoutPos π (S a)) + Fintype.card A) := by
        rw [← mul_sum, sum_add_distrib, ← mul_sum]
        simp

/-! ## Exact coupling under a common deterministic oracle

Model for `thm:adaptive-oracle-coupling`.  A run is driven by a controller that sees the
history of terminal observations, the reply of a deterministic certificate-and-witness
oracle on that history, and a controller tape `ω`; it requests the next terminal sample,
which is read from the common reward tape `rew`. -/

section Coupling

variable {Z X Reply Ω σ σ' : Type*}

/-- A controller: `next` chooses the next terminal to sample from the history, the oracle
reply and the controller tape; `stop` is the stopping bit computed from history and reply. -/
structure Controller (Z X Reply Ω : Type*) where
  next : List (Z × X) → Reply → Ω → Z
  stop : List (Z × X) → Reply → Bool

/-- History of observations after `n` rollouts, under oracle `oracle`, reward tape `rew`
(`rew n z` is the reward revealed if terminal `z` is sampled at rollout `n`) and controller
tape `ω`. -/
def history (oracle : List (Z × X) → Reply) (ctrl : Controller Z X Reply Ω)
    (rew : ℕ → Z → X) (ω : Ω) : ℕ → List (Z × X)
  | 0 => []
  | n + 1 =>
    history oracle ctrl rew ω n ++
      [(ctrl.next (history oracle ctrl rew ω n) (oracle (history oracle ctrl rew ω n)) ω,
        rew n (ctrl.next (history oracle ctrl rew ω n)
          (oracle (history oracle ctrl rew ω n)) ω))]

/-- Oracle reply (certificate, witness, recommendation) after `n` rollouts. -/
def replyAt (oracle : List (Z × X) → Reply) (ctrl : Controller Z X Reply Ω)
    (rew : ℕ → Z → X) (ω : Ω) (n : ℕ) : Reply :=
  oracle (history oracle ctrl rew ω n)

/-- The run has its stopping bit set after `n` rollouts. -/
def stoppedAt (oracle : List (Z × X) → Reply) (ctrl : Controller Z X Reply Ω)
    (rew : ℕ → Z → X) (ω : Ω) (n : ℕ) : Prop :=
  ctrl.stop (history oracle ctrl rew ω n) (replyAt oracle ctrl rew ω n) = true

/-- Stopping time: the first rollout count at which the stopping bit is set (`⊤` if never). -/
noncomputable def stopTime (oracle : List (Z × X) → Reply) (ctrl : Controller Z X Reply Ω)
    (rew : ℕ → Z → X) (ω : Ω) : ℕ∞ :=
  sInf ((fun n : ℕ => (n : ℕ∞)) '' {n | stoppedAt oracle ctrl rew ω n})

/-- **Coupling induction.**  If a second oracle agrees with the first on every history
reached by the first run, the two runs have identical histories. -/
theorem history_eq_of_agree (o o' : List (Z × X) → Reply) (ctrl : Controller Z X Reply Ω)
    (rew : ℕ → Z → X) (ω : Ω)
    (h : ∀ n, o' (history o ctrl rew ω n) = o (history o ctrl rew ω n)) :
    ∀ n, history o' ctrl rew ω n = history o ctrl rew ω n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [history]
    rw [ih, h n]

/-- Under the hypothesis of `history_eq_of_agree`, observations, oracle replies
(recommendations) and stopping times coincide. -/
theorem run_eq_of_agree (o o' : List (Z × X) → Reply) (ctrl : Controller Z X Reply Ω)
    (rew : ℕ → Z → X) (ω : Ω)
    (h : ∀ n, o' (history o ctrl rew ω n) = o (history o ctrl rew ω n)) :
    (∀ n, history o' ctrl rew ω n = history o ctrl rew ω n) ∧
    (∀ n, replyAt o' ctrl rew ω n = replyAt o ctrl rew ω n) ∧
    stopTime o' ctrl rew ω = stopTime o ctrl rew ω := by
  have hh := history_eq_of_agree o o' ctrl rew ω h
  have hr : ∀ n, replyAt o' ctrl rew ω n = replyAt o ctrl rew ω n := fun n => by
    unfold replyAt
    rw [hh n, h n]
  refine ⟨hh, hr, ?_⟩
  have hs : {n | stoppedAt o' ctrl rew ω n} = {n | stoppedAt o ctrl rew ω n} := by
    ext n
    show stoppedAt o' ctrl rew ω n ↔ stoppedAt o ctrl rew ω n
    unfold stoppedAt
    rw [hh n, hr n]
  unfold stopTime
  rw [hs]

/-- An implementation of an oracle: an internal state updated by each observation, and a
reply read off the state. -/
structure OracleImpl (σ Obs Reply : Type*) where
  init : σ
  step : σ → Obs → σ
  reply : σ → Reply

/-- The oracle exposed by an implementation: its reply as a function of the history. -/
def OracleImpl.answer {Obs : Type*} (I : OracleImpl σ Obs Reply) (h : List Obs) : Reply :=
  I.reply (h.foldl I.step I.init)

/-- **Exact coupling** (`thm:adaptive-oracle-coupling`, first sentence).  Two
implementations, with arbitrary internal states, that expose the same deterministic
certificate-and-witness oracle induce identical observations, recommendations and stopping
times under common reward and controller tapes. -/
theorem exact_coupling (I : OracleImpl σ (Z × X) Reply) (J : OracleImpl σ' (Z × X) Reply)
    (hIJ : ∀ h, J.answer h = I.answer h) (ctrl : Controller Z X Reply Ω)
    (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history J.answer ctrl rew ω n = history I.answer ctrl rew ω n) ∧
    (∀ n, replyAt J.answer ctrl rew ω n = replyAt I.answer ctrl rew ω n) ∧
    stopTime J.answer ctrl rew ω = stopTime I.answer ctrl rew ω :=
  run_eq_of_agree _ _ ctrl rew ω (fun _ => hIJ _)

end Coupling

/-! ## Max-circuits over terminal values -/

/-- A monitor `max`-circuit over terminals `Z`: a leaf reads one terminal, a gate takes the
maximum of its children.  A circuit DAG with sharing is represented by its unfolding; sharing
does not affect the computed function.  A unary output gate is `gate [c]`. -/
inductive MaxCircuit (Z : Type*) where
  | leaf : Z → MaxCircuit Z
  | gate : List (MaxCircuit Z) → MaxCircuit Z

namespace MaxCircuit

section Eval

variable {Z α : Type*} [SemilatticeSup α] [OrderBot α]

mutual
  /-- Value of a circuit on a terminal vector `f` (an empty gate evaluates to `⊥`). -/
  def eval (f : Z → α) : MaxCircuit Z → α
    | leaf z => f z
    | gate cs => evalList f cs
  /-- Maximum of the values of a list of circuits. -/
  def evalList (f : Z → α) : List (MaxCircuit Z) → α
    | [] => ⊥
    | c :: cs => eval f c ⊔ evalList f cs
end

mutual
  /-- Terminal support of a circuit. -/
  def supp [DecidableEq Z] : MaxCircuit Z → Finset Z
    | leaf z => {z}
    | gate cs => suppList cs
  /-- Union of the supports of a list of circuits. -/
  def suppList [DecidableEq Z] : List (MaxCircuit Z) → Finset Z
    | [] => ∅
    | c :: cs => supp c ∪ suppList cs
end

mutual
  /-- **A max-circuit computes its support maximum**, for every terminal vector. -/
  theorem eval_eq_sup [DecidableEq Z] (f : Z → α) :
      ∀ c : MaxCircuit Z, eval f c = (supp c).sup f
    | leaf z => by simp [eval, supp]
    | gate cs => by
      simp only [eval, supp]
      exact evalList_eq_sup f cs
  theorem evalList_eq_sup [DecidableEq Z] (f : Z → α) :
      ∀ cs : List (MaxCircuit Z), evalList f cs = (suppList cs).sup f
    | [] => by simp [evalList, suppList]
    | c :: cs => by
      simp only [evalList, suppList, Finset.sup_union]
      rw [eval_eq_sup f c, evalList_eq_sup f cs]
end

/-- Circuits with the same terminal support compute the same function of every terminal
vector.  This covers unary bypass, interning, and replacement of a root support by a
dyadic-block circuit (`prop:representation-coupling`). -/
theorem eval_eq_of_supp_eq [DecidableEq Z] (f : Z → α) {c c' : MaxCircuit Z}
    (h : supp c = supp c') : eval f c = eval f c' := by
  rw [eval_eq_sup, eval_eq_sup, h]

lemma evalList_le_iff (f : Z → α) (cs : List (MaxCircuit Z)) (x : α) :
    evalList f cs ≤ x ↔ ∀ c ∈ cs, eval f c ≤ x := by
  induction cs with
  | nil => simp [evalList]
  | cons c cs ih => simp [evalList, ih]

lemma eval_le_evalList (f : Z → α) {cs : List (MaxCircuit Z)} {c : MaxCircuit Z}
    (hc : c ∈ cs) : eval f c ≤ evalList f cs :=
  (evalList_le_iff f cs _).1 le_rfl c hc

/-- **Unary bypass**: a unary gate computes the value of its child. -/
theorem eval_unary (f : Z → α) (c : MaxCircuit Z) : eval f (gate [c]) = eval f c := by
  simp [eval, evalList]

/-- **Interning**: gates with identical child sets compute the same value, whatever the
order and multiplicity of their child lists (idempotence and commutativity of `max`). -/
theorem eval_gate_congr (f : Z → α) {cs cs' : List (MaxCircuit Z)}
    (h : ∀ c, c ∈ cs ↔ c ∈ cs') : eval f (gate cs) = eval f (gate cs') := by
  simp only [eval]
  apply le_antisymm
  · exact (evalList_le_iff f cs _).2 (fun c hc => eval_le_evalList f ((h c).1 hc))
  · exact (evalList_le_iff f cs' _).2 (fun c hc => eval_le_evalList f ((h c).2 hc))

lemma mem_suppList [DecidableEq Z] (cs : List (MaxCircuit Z)) (z : Z) :
    z ∈ suppList cs ↔ ∃ c ∈ cs, z ∈ supp c := by
  induction cs with
  | nil => simp [suppList]
  | cons c cs ih => simp [suppList, ih]

lemma eval_mono [DecidableEq Z] {f g : Z → α} (h : ∀ z, f z ≤ g z) (c : MaxCircuit Z) :
    eval f c ≤ eval g c := by
  rw [eval_eq_sup, eval_eq_sup]
  exact Finset.sup_mono_fun (fun z _ => h z)

lemma evalList_mono [DecidableEq Z] {f g : Z → α} (h : ∀ z, f z ≤ g z)
    (cs : List (MaxCircuit Z)) : evalList f cs ≤ evalList g cs :=
  eval_mono h (gate cs)

end Eval

section Dyadic

variable {Z α : Type*} [SemilatticeSup α] [OrderBot α] [Fintype Z] [DecidableEq Z]

/-- The shared gate of a dyadic block `B` under layout `π`: the maximum over all terminals
whose position lies in `B`.  It does not depend on any root action. -/
noncomputable def blockGate {M : ℕ} (π : Z ≃ Fin M) (B : Finset ℕ) : MaxCircuit Z :=
  gate ((univ.filter (fun z => (π z : ℕ) ∈ B)).toList.map leaf)

/-- The dyadic-block circuit of a root action: a root gate over the shared block gates of a
cover `C`. -/
noncomputable def dyadicCircuit {M : ℕ} (π : Z ≃ Fin M) (C : Finset (Finset ℕ)) :
    MaxCircuit Z :=
  gate (C.toList.map (blockGate π))

lemma supp_blockGate {M : ℕ} (π : Z ≃ Fin M) (B : Finset ℕ) :
    supp (blockGate π B) = univ.filter (fun z => (π z : ℕ) ∈ B) := by
  ext z
  simp only [blockGate, supp, mem_suppList, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨c, ⟨y, hy, rfl⟩, hz⟩
    simp only [supp, Finset.mem_singleton] at hz
    rwa [hz]
  · intro hz
    exact ⟨leaf z, ⟨z, hz, rfl⟩, by simp [supp]⟩

/-- The dyadic-block circuit built from a dyadic cover of the positions of `S` has terminal
support exactly `S`. -/
theorem supp_dyadicCircuit {M : ℕ} (π : Z ≃ Fin M) {C : Finset (Finset ℕ)} {S : Finset Z}
    (hC : IsDyadicCover C (layoutPos π S)) : supp (dyadicCircuit π C) = S := by
  ext z
  simp only [dyadicCircuit, supp, mem_suppList, List.mem_map, Finset.mem_toList]
  have key : (π z : ℕ) ∈ layoutPos π S ↔ z ∈ S := by
    rw [mem_layoutPos]
    constructor
    · rintro ⟨h, hs⟩
      simpa using hs
    · intro hz
      exact ⟨(π z).2, by simpa using hz⟩
  constructor
  · rintro ⟨c, ⟨B, hB, rfl⟩, hz⟩
    rw [supp_blockGate, Finset.mem_filter] at hz
    exact key.1 (hC.subset hB hz.2)
  · intro hz
    have := key.2 hz
    rw [← hC.biUnion_eq, Finset.mem_biUnion] at this
    obtain ⟨B, hB, hzB⟩ := this
    refine ⟨blockGate π B, ⟨B, hB, rfl⟩, ?_⟩
    rw [supp_blockGate, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hzB⟩

/-- **Dyadic interval decomposition preserves root values**: under any layout and any
dyadic cover of a root support `S`, the shared dyadic-block circuit computes the support
maximum `max_{z ∈ S} f z` for every terminal vector `f`. -/
theorem eval_dyadicCircuit {M : ℕ} (π : Z ≃ Fin M) {C : Finset (Finset ℕ)} {S : Finset Z}
    (hC : IsDyadicCover C (layoutPos π S)) (f : Z → α) :
    eval f (dyadicCircuit π C) = S.sup f := by
  rw [eval_eq_sup, supp_dyadicCircuit π hC]

end Dyadic

/-- On real terminal values (embedded in `WithBot ℝ`), a circuit with nonempty support `S`
computes the root value `val S hS f` of `JointRootCert.Basic`. -/
theorem eval_coe_eq_val {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    {c : MaxCircuit Z} {S : Finset Z} (hS : S.Nonempty) (hc : supp c = S) (f : Z → ℝ) :
    eval (fun z => (f z : WithBot ℝ)) c = ((val S hS f : ℝ) : WithBot ℝ) := by
  rw [eval_eq_sup, hc, val, Finset.coe_sup']
  rfl

section Retirement

variable {Z β : Type*} [LinearOrder β] [OrderBot β]

/-- Removing a child whose value is strictly below the gate value does not change the gate
value. -/
lemma evalList_erase_of_lt (g : Z → β) {cs cs' : List (MaxCircuit Z)} {c : MaxCircuit Z}
    (hlt : eval g c < evalList g cs) (hcs' : ∀ d, d ∈ cs' ↔ d ∈ cs ∧ d ≠ c) :
    evalList g cs' = evalList g cs := by
  apply le_antisymm
  · exact (evalList_le_iff g cs' _).2
      (fun d hd => eval_le_evalList g ((hcs' d).1 hd).1)
  · by_contra hnot
    have hlt' : evalList g cs' < evalList g cs := lt_of_not_ge hnot
    have hle : evalList g cs ≤ max (evalList g cs') (eval g c) := by
      refine (evalList_le_iff g cs _).2 (fun d hd => ?_)
      by_cases hdc : d = c
      · rw [hdc]
        exact le_max_right _ _
      · exact (eval_le_evalList g ((hcs' d).2 ⟨hd, hdc⟩)).trans (le_max_left _ _)
    exact absurd hle (not_le.2 (max_lt hlt' hlt))

/-- **Strict dominance retirement** (`prop:representation-coupling`, second sentence; the
gate-level content of `prop:ta-coupled`(i)).  Let `v = gate cs` and let a child `c` satisfy
`u_t(c) < l_t(v)` at time `t`.  If the terminal boxes are nested and nonempty
(`l_t ≤ l_s ≤ u_s ≤ u_t`), then at the later time `s` the gate with `c` removed
(`cs'`) has the same lower and upper endpoints as `v`: the incidence `(v, c)` never
determines either endpoint again.  In particular `cs'` is nonempty. -/
theorem retire_preserves [DecidableEq Z] {lt ut ls us : Z → β}
    {cs cs' : List (MaxCircuit Z)} {c : MaxCircuit Z}
    (hl : ∀ z, lt z ≤ ls z) (hu : ∀ z, us z ≤ ut z) (hlu : ∀ z, ls z ≤ us z)
    (hdom : eval ut c < eval lt (gate cs))
    (hcs' : ∀ d, d ∈ cs' ↔ d ∈ cs ∧ d ≠ c) :
    eval ls (gate cs') = eval ls (gate cs) ∧ eval us (gate cs') = eval us (gate cs) ∧
      cs' ≠ [] := by
  simp only [eval] at hdom ⊢
  have h1 : eval us c < evalList ls cs :=
    lt_of_le_of_lt (eval_mono hu c) (lt_of_lt_of_le hdom (evalList_mono hl cs))
  have h2 : eval ls c < evalList ls cs := lt_of_le_of_lt (eval_mono hlu c) h1
  have h3 : eval us c < evalList us cs := lt_of_lt_of_le h1 (evalList_mono hlu cs)
  have e1 := evalList_erase_of_lt ls h2 hcs'
  refine ⟨e1, evalList_erase_of_lt us h3 hcs', ?_⟩
  rintro rfl
  rw [← e1] at h2
  simp [evalList] at h2

end Retirement

end MaxCircuit

/-! ## Trajectory coupling across circuit representations -/

section CircuitCoupling

open MaxCircuit

variable {Z X Ω A β : Type*} [SemilatticeSup β] [OrderBot β] [DecidableEq Z]

/-- The monitor oracle of a family `R` of root circuits: from the cumulative terminal box
`box h = (l, u)` of the history `h`, the root intervals `[l(a), u(a)]` of all root actions.
Leaders, optimistic leaders and stopping bits are functions of this reply. -/
def circuitOracle (box : List (Z × X) → (Z → β) × (Z → β)) (R : A → MaxCircuit Z) :
    List (Z × X) → A → β × β :=
  fun h a => (eval (box h).1 (R a), eval (box h).2 (R a))

/-- Root intervals depend only on the terminal supports of the root circuits. -/
theorem circuitOracle_eq_of_supp_eq (box : List (Z × X) → (Z → β) × (Z → β))
    (R R' : A → MaxCircuit Z) (h : ∀ a, supp (R' a) = supp (R a)) :
    circuitOracle box R' = circuitOracle box R := by
  funext hist a
  simp only [circuitOracle]
  rw [eval_eq_of_supp_eq _ (h a), eval_eq_of_supp_eq _ (h a)]

/-- **Trajectory coupling across circuit representations**
(`prop:representation-coupling`, first sentence).  Two monitor circuits whose root gates
have the same terminal supports in the same root-action order (as after unary bypass,
interning, or dyadic-block replacement: `eval_unary`, `eval_gate_congr`,
`supp_dyadicCircuit`) expose the same root intervals for every terminal box, hence induce
identical histories, replies (leaders) and stopping times for any controller. -/
theorem representation_coupling (box : List (Z × X) → (Z → β) × (Z → β))
    (R R' : A → MaxCircuit Z) (h : ∀ a, supp (R' a) = supp (R a))
    (ctrl : Controller Z X (A → β × β) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history (circuitOracle box R') ctrl rew ω n
        = history (circuitOracle box R) ctrl rew ω n) ∧
    (∀ n, replyAt (circuitOracle box R') ctrl rew ω n
        = replyAt (circuitOracle box R) ctrl rew ω n) ∧
    stopTime (circuitOracle box R') ctrl rew ω = stopTime (circuitOracle box R) ctrl rew ω := by
  rw [circuitOracle_eq_of_supp_eq box R R' h]
  exact ⟨fun _ => rfl, fun _ => rfl, rfl⟩

omit [DecidableEq Z] in
/-- **Coupling under online retirement** (`prop:representation-coupling`, second
sentence, modular form).  Let `R' hist` be the history-dependent circuits obtained from `R`
by retiring incidences.  If along the run of `R` the retired circuits keep the root
endpoints of `R` (which `MaxCircuit.retire_preserves` supplies for each strict-dominance
retirement under nested boxes), then the retired monitor induces the same histories,
replies and stopping times as the unretired one. -/
theorem retirement_coupling (box : List (Z × X) → (Z → β) × (Z → β))
    (R : A → MaxCircuit Z) (R' : List (Z × X) → A → MaxCircuit Z)
    (ctrl : Controller Z X (A → β × β) Ω) (rew : ℕ → Z → X) (ω : Ω)
    (hkeep : ∀ n a,
      eval (box (history (circuitOracle box R) ctrl rew ω n)).1
          (R' (history (circuitOracle box R) ctrl rew ω n) a)
        = eval (box (history (circuitOracle box R) ctrl rew ω n)).1 (R a) ∧
      eval (box (history (circuitOracle box R) ctrl rew ω n)).2
          (R' (history (circuitOracle box R) ctrl rew ω n) a)
        = eval (box (history (circuitOracle box R) ctrl rew ω n)).2 (R a)) :
    let o' : List (Z × X) → A → β × β :=
      fun h a => (eval (box h).1 (R' h a), eval (box h).2 (R' h a))
    (∀ n, history o' ctrl rew ω n = history (circuitOracle box R) ctrl rew ω n) ∧
    (∀ n, replyAt o' ctrl rew ω n = replyAt (circuitOracle box R) ctrl rew ω n) ∧
    stopTime o' ctrl rew ω = stopTime (circuitOracle box R) ctrl rew ω := by
  intro o'
  apply run_eq_of_agree
  intro n
  funext a
  simp only [o', circuitOracle]
  rw [(hkeep n a).1, (hkeep n a).2]

omit [DecidableEq Z] in
/-- **Unrestricted circuit retention** (`prop:unrestricted-compiler`, semantic part).  An
implementation that retains (a copy of) the original monitor circuit, i.e. whose exposed
oracle is that of the original circuit family `R`, reproduces the run of the original
implementation.  The `O(|V| + |E|)` copy cost is not formalized. -/
theorem retained_circuit_coupling {σ σ' : Type*}
    (box : List (Z × X) → (Z → β) × (Z → β)) (R : A → MaxCircuit Z)
    (I : OracleImpl σ (Z × X) (A → β × β)) (J : OracleImpl σ' (Z × X) (A → β × β))
    (hI : ∀ h, I.answer h = circuitOracle box R h)
    (hJ : ∀ h, J.answer h = circuitOracle box R h)
    (ctrl : Controller Z X (A → β × β) Ω) (rew : ℕ → Z → X) (ω : Ω) :
    (∀ n, history J.answer ctrl rew ω n = history I.answer ctrl rew ω n) ∧
    (∀ n, replyAt J.answer ctrl rew ω n = replyAt I.answer ctrl rew ω n) ∧
    stopTime J.answer ctrl rew ω = stopTime I.answer ctrl rew ω :=
  exact_coupling I J (fun h => (hJ h).trans (hI h).symm) ctrl rew ω

end CircuitCoupling

/-! ## Cost accounting for discovery and maintenance -/

section Cost

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Active incoming parent degree `d_F^-(v)` of gate `v` in the incidence set `F`
(incidences are pairs `(parent, child)`). -/
def inDeg (F : Finset (V × V)) (v : V) : ℕ := (F.filter (fun e => e.2 = v)).card

/-- One wave's delivery volume `Σ_v b(v) d_F^-(v)`. -/
def deliveryVolume (F : Finset (V × V)) (b : V → ℕ) : ℕ := ∑ v, b v * inDeg F v

lemma deliveryVolume_eq_sum (F : Finset (V × V)) (b : V → ℕ) :
    deliveryVolume F b = ∑ e ∈ F, b e.2 := by
  unfold deliveryVolume inDeg
  rw [← sum_fiberwise F (fun e => e.2) (fun e => b e.2)]
  apply sum_congr rfl
  intro v _
  have : ∑ e ∈ F with e.2 = v, b e.2 = ∑ e ∈ F with e.2 = v, b v :=
    sum_congr rfl (fun e he => by rw [(mem_filter.1 he).2])
  rw [this, sum_const, smul_eq_mul, mul_comm]

/-- The deliveries of a wave over live incidences `F`: one per live incidence `(p, v)` and
changed endpoint of the child `v` (`ch v ⊆ {lower, upper}`). -/
def deliverySet (F : Finset (V × V)) (ch : V → Finset (Fin 2)) :
    Finset ((V × V) × Fin 2) :=
  (F ×ˢ univ).filter (fun p => p.2 ∈ ch p.1.2)

lemma card_deliverySet (F : Finset (V × V)) (ch : V → Finset (Fin 2)) :
    (deliverySet F ch).card = deliveryVolume F (fun v => (ch v).card) := by
  rw [deliveryVolume_eq_sum]
  unfold deliverySet
  rw [card_filter, sum_product]
  apply sum_congr rfl
  intro e _
  rw [← card_filter]
  congr 1
  ext k
  simp

/-- Cumulative pre-update delivery volume `S_R^+` of `eq:s-plus-minus`, with
`b t v = b_t(v)` and `F t = F_t`. -/
def Splus (τ : ℕ) (F : ℕ → Finset (V × V)) (b : ℕ → V → ℕ) : ℕ :=
  ∑ t ∈ Icc 1 τ, deliveryVolume (F (t - 1)) (b t)

/-- Cumulative post-update delivery volume `S_R^-` of `eq:s-plus-minus`. -/
def Sminus (τ : ℕ) (F : ℕ → Finset (V × V)) (b : ℕ → V → ℕ) : ℕ :=
  ∑ t ∈ Icc 1 τ, deliveryVolume (F t) (b t)

/-- With retirement only, `S^- ≤ S^+`. -/
lemma Sminus_le_Splus (τ : ℕ) (F : ℕ → Finset (V × V)) (b : ℕ → V → ℕ)
    (hF : ∀ t ∈ Icc 1 τ, F t ⊆ F (t - 1)) : Sminus τ F b ≤ Splus τ F b := by
  apply sum_le_sum
  intro t ht
  rw [deliveryVolume_eq_sum, deliveryVolume_eq_sum]
  exact sum_le_sum_of_subset (hF t ht)

/-- Upper delivery count: if every delivery of wave `t` goes along an incidence live before
the wave and carries a changed endpoint of its child, the number of deliveries through `τ`
is at most `S^+`. -/
theorem deliveries_le_Splus (τ : ℕ) (F : ℕ → Finset (V × V)) (ch : ℕ → V → Finset (Fin 2))
    (Dl : ℕ → Finset ((V × V) × Fin 2))
    (h : ∀ t ∈ Icc 1 τ, Dl t ⊆ deliverySet (F (t - 1)) (ch t)) :
    ∑ t ∈ Icc 1 τ, (Dl t).card ≤ Splus τ F (fun t v => (ch t v).card) := by
  apply sum_le_sum
  intro t ht
  rw [← card_deliverySet]
  exact card_le_card (h t ht)

/-- Lower delivery count: if every changed endpoint is delivered along every incidence still
live after the wave, the number of deliveries through `τ` is at least `S^-`. -/
theorem Sminus_le_deliveries (τ : ℕ) (F : ℕ → Finset (V × V))
    (ch : ℕ → V → Finset (Fin 2)) (Dl : ℕ → Finset ((V × V) × Fin 2))
    (h : ∀ t ∈ Icc 1 τ, deliverySet (F t) (ch t) ⊆ Dl t) :
    Sminus τ F (fun t v => (ch t v).card) ≤ ∑ t ∈ Icc 1 τ, (Dl t).card := by
  apply sum_le_sum
  intro t ht
  rw [← card_deliverySet]
  exact card_le_card (h t ht)

/-- **Upper bound `eq:prop-rep-upper`, accounting form** (`prop:representation-cost`).
Hypotheses stand for the engine's charges: the total work `W` is at most the shared work
`H`, the compilation work `P`, `c` per gate and incidence for allocation and disposal,
`c · logD` per incidence for its single retirement, and `c · logD` per delivery; and every
delivery goes along a pre-wave live incidence with a changed endpoint.  Then
`W ≤ c (H + P + n + e + (S^+ + e) logD)`. -/
theorem work_upper (τ : ℕ) (F : ℕ → Finset (V × V)) (ch : ℕ → V → Finset (Fin 2))
    (Dl : ℕ → Finset ((V × V) × Fin 2))
    (hD : ∀ t ∈ Icc 1 τ, Dl t ⊆ deliverySet (F (t - 1)) (ch t))
    (W H P n e logD c : ℕ) (hc : 1 ≤ c)
    (hW : W ≤ H + P + c * (n + e) + c * logD * e + c * logD * ∑ t ∈ Icc 1 τ, (Dl t).card) :
    W ≤ c * (H + P + n + e + (Splus τ F (fun t v => (ch t v).card) + e) * logD) := by
  have h1 := deliveries_le_Splus τ F ch Dl hD
  have h2 := Nat.mul_le_mul_left (c * logD) h1
  have h3 := Nat.mul_le_mul_right H hc
  have h4 := Nat.mul_le_mul_right P hc
  nlinarith

/-- **Lower bound `Ω(P_C + S_C^-)`, accounting form** (`prop:representation-cost`).  If the
work `W` pays the compilation work `P` and one operation per delivery, and the
incidence-delivery contract delivers every changed endpoint along every incidence still
live after the wave, then `P + S^- ≤ W`. -/
theorem work_lower (τ : ℕ) (F : ℕ → Finset (V × V)) (ch : ℕ → V → Finset (Fin 2))
    (Dl : ℕ → Finset ((V × V) × Fin 2))
    (hD : ∀ t ∈ Icc 1 τ, deliverySet (F t) (ch t) ⊆ Dl t)
    (W P : ℕ) (hW : P + ∑ t ∈ Icc 1 τ, (Dl t).card ≤ W) :
    P + Sminus τ F (fun t v => (ch t v).card) ≤ W :=
  (Nat.add_le_add_left (Sminus_le_deliveries τ F ch Dl hD) P).trans hW

/-- **Condition (R)** (`eq:representation-condition`).  Along any family of instances
(filter `l`), if the direct-graph work is `O` of its upper expression `XG`, the compiled
work is `Ω` of its lower expression `YC = P_C + S_C^-`, and `XG = o(YC)`, then the direct
graph work is `o` of the compiled work. -/
theorem representation_advantage {ι : Type*} {l : Filter ι} {WG XG YC WC : ι → ℝ}
    (hG : WG =O[l] XG) (hR : XG =o[l] YC) (hC : YC =O[l] WC) : WG =o[l] WC :=
  (hG.trans_isLittleO hR).trans_isBigO hC

end Cost

/-! ## The parity grid and the every-layout lower bound -/

section Layout

/-- **Every-layout run count.**  Let `acts` be a family of root actions with supports `S a`
over terminals laid out by `π : T ≃ Fin N`.  If any two distinct terminals are separated by
at least `r` of the supports (Hamming distance of membership vectors), then the total
number of runs satisfies `(N - 1) r ≤ 2 Σ_a runs`. -/
theorem total_runs_lower {T A : Type*} [DecidableEq T] {N : ℕ} (π : T ≃ Fin N)
    (acts : Finset A) (S : A → Finset T) (r : ℕ)
    (hsep : ∀ t t', t ≠ t' → r ≤ (acts.filter (fun a => ¬ (t ∈ S a ↔ t' ∈ S a))).card) :
    (N - 1) * r ≤ 2 * ∑ a ∈ acts, runs (layoutPos π (S a)) := by
  calc (N - 1) * r = ∑ _s ∈ range (N - 1), r := by simp
    _ ≤ ∑ s ∈ range (N - 1), (acts.filter (fun a =>
          ¬ (s ∈ layoutPos π (S a) ↔ s + 1 ∈ layoutPos π (S a)))).card := by
        apply sum_le_sum
        intro s hs
        have hs1 : s + 1 < N := by
          have := mem_range.1 hs
          omega
        have hs0 : s < N := by omega
        have hne : π.symm ⟨s, hs0⟩ ≠ π.symm ⟨s + 1, hs1⟩ := by
          intro h
          have := congrArg Fin.val (π.symm.injective h)
          simp at this
        refine (hsep _ _ hne).trans (le_of_eq ?_)
        congr 1
        apply filter_congr
        intro a _
        rw [mem_layoutPos, mem_layoutPos]
        constructor
        · intro h h'
          apply h
          constructor
          · intro ht
            exact (h'.1 ⟨hs0, ht⟩).2
          · intro ht
            exact (h'.2 ⟨hs1, ht⟩).2
        · intro h h'
          apply h
          constructor
          · rintro ⟨_, ht⟩
            exact ⟨hs1, h'.1 ht⟩
          · rintro ⟨_, ht⟩
            exact ⟨hs0, h'.2 ht⟩
    _ = ∑ a ∈ acts, transitions (layoutPos π (S a)) N := by
        simp only [transitions, card_filter]
        exact sum_comm
    _ ≤ ∑ a ∈ acts, 2 * runs (layoutPos π (S a)) :=
        sum_le_sum (fun a _ => transitions_le _ _)
    _ = 2 * ∑ a ∈ acts, runs (layoutPos π (S a)) := (mul_sum _ _ _).symm

end Layout

section ParityGrid

/-- Vectors of `𝔽₂^k`; there are `r = 2^k` of them. -/
abbrev Mask (k : ℕ) := Fin k → ZMod 2

/-- Canonical terminals of the parity-grid DAG: the `r^2` grid terminals `(i, j)` and the
direct winning terminal `w^* = none`. -/
abbrev GridTerminal (k : ℕ) := Option (Mask k × Mask k)

/-- Index of a parity root action: `(true, a, b)` is the row action `A_{a,b}^row`,
`(false, a, b)` the column action `A_{a,b}^col`. -/
abbrev ParityIndex (k : ℕ) := Bool × Mask k × ZMod 2

/-- Membership of a terminal in the support of a parity action:
`A_{a,b}^row = max_{⟨a,i⟩ = b} R_i` with `R_i = max_j (i, j)` has support
`{(i, j) : ⟨a, i⟩ = b}`; columns symmetrically; `w^*` is in no parity support. -/
def parityMem {k : ℕ} (p : ParityIndex k) : GridTerminal k → Prop
  | none => False
  | some x => p.2.1 ⬝ᵥ (if p.1 then x.1 else x.2) = p.2.2

instance {k : ℕ} (p : ParityIndex k) : DecidablePred (parityMem p) := fun t =>
  match t with
  | none => inferInstanceAs (Decidable False)
  | some x => inferInstanceAs (Decidable (p.2.1 ⬝ᵥ (if p.1 then x.1 else x.2) = p.2.2))

/-- Terminal support of a parity action. -/
def paritySupp {k : ℕ} (p : ParityIndex k) : Finset (GridTerminal k) :=
  univ.filter (parityMem p)

/-- The `d = 4(r-1)` parity root actions: nonzero mask, either orientation, either bit. -/
def parityActions (k : ℕ) : Finset (ParityIndex k) :=
  univ.filter (fun p => p.2.1 ≠ 0)

lemma card_mask (k : ℕ) : (univ : Finset (Mask k)).card = 2 ^ k := by
  rw [card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma card_mask_ne_zero (k : ℕ) :
    (univ.filter (fun a : Mask k => a ≠ 0)).card = 2 ^ k - 1 := by
  rw [filter_ne', card_erase_of_mem (mem_univ _), card_mask]

/-- There are `d = 4(r - 1)` parity actions. -/
lemma card_parityActions (k : ℕ) : (parityActions k).card = 4 * (2 ^ k - 1) := by
  have h : parityActions k
      = (univ : Finset Bool) ×ˢ ((univ.filter (fun a : Mask k => a ≠ 0))
          ×ˢ (univ : Finset (ZMod 2))) := by
    ext ⟨f, a, b⟩
    simp [parityActions]
  rw [h, card_product, card_product, card_mask_ne_zero]
  have h2 : (univ : Finset (ZMod 2)).card = 2 := by rw [card_univ, ZMod.card]
  rw [h2]
  simp
  omega

/-- For `v ≠ 0`, at least half of the masks `a` have `⟨a, v⟩ = 1` (exactly `r/2`). -/
lemma card_dot_eq_one {k : ℕ} (v : Mask k) (hv : v ≠ 0) :
    2 ^ k ≤ 2 * (univ.filter (fun a : Mask k => a ⬝ᵥ v = 1)).card := by
  obtain ⟨l, hl⟩ := Function.ne_iff.1 hv
  have hl1 : v l = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hl
  have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Mask k)))
    (fun a => a ⬝ᵥ v = 1)
  have hinj : (univ.filter (fun a : Mask k => ¬ a ⬝ᵥ v = 1)).card
      ≤ (univ.filter (fun a : Mask k => a ⬝ᵥ v = 1)).card := by
    apply card_le_card_of_injOn (fun a => a + Pi.single l 1)
    · intro a ha
      have ha' : ¬ a ⬝ᵥ v = 1 := (mem_filter.1 (mem_coe.1 ha)).2
      refine mem_coe.2 (mem_filter.2 ⟨mem_univ _, ?_⟩)
      rw [add_dotProduct, single_dotProduct, hl1]
      exact (by decide : ∀ x : ZMod 2, ¬ x = 1 → x + 1 * 1 = 1) _ ha'
    · intro a _ b _ h
      exact add_right_cancel h
  have hcard := card_mask k
  omega

/-- A grid terminal against `w^*`: at least `r` parity supports contain the grid terminal
(exactly `2(r-1)`), and none contains `w^*`. -/
lemma parity_sep_some_none {k : ℕ} (hk : 1 ≤ k) (x : Mask k × Mask k) :
    2 ^ k ≤ ((parityActions k).filter
      (fun p => ¬ (parityMem p (some x) ↔ parityMem p none))).card := by
  have hsrc : ((univ.filter (fun a : Mask k => a ≠ 0)) ×ˢ (univ : Finset Bool)).card
      = (2 ^ k - 1) * 2 := by
    rw [card_product, card_mask_ne_zero]
    simp
  have h2k : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hle : ((univ.filter (fun a : Mask k => a ≠ 0)) ×ˢ (univ : Finset Bool)).card
      ≤ ((parityActions k).filter
        (fun p => ¬ (parityMem p (some x) ↔ parityMem p none))).card := by
    apply card_le_card_of_injOn
      (fun q : Mask k × Bool => ((q.2, q.1, q.1 ⬝ᵥ (if q.2 then x.1 else x.2)) : ParityIndex k))
    · rintro ⟨a, f⟩ hq
      have ha : a ≠ 0 := (mem_filter.1 (mem_product.1 (mem_coe.1 hq)).1).2
      refine mem_coe.2 (mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ha⟩, ?_⟩)
      simp [parityMem]
    · rintro ⟨a, f⟩ _ ⟨a', f'⟩ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2.1 h.1
  omega

/-- **Hamming separation** (Step 2 of the proof of `thm:coded-covers`).  Any two distinct
terminals of the parity grid (grid terminals or `w^*`) are separated by at least `r = 2^k`
of the `d` parity-action supports. -/
theorem parity_separation {k : ℕ} (hk : 1 ≤ k) (t t' : GridTerminal k) (h : t ≠ t') :
    2 ^ k ≤ ((parityActions k).filter
      (fun p => ¬ (parityMem p t ↔ parityMem p t'))).card := by
  rcases t with _ | x <;> rcases t' with _ | y
  · exact absurd rfl h
  · have := parity_sep_some_none hk y
    rwa [filter_congr (fun p _ => not_congr (Iff.comm
      (a := parityMem p (some y)) (b := parityMem p none)))] at this
  · exact parity_sep_some_none hk x
  · have hxy : x ≠ y := fun e => h (congrArg some e)
    obtain ⟨f, hf⟩ : ∃ f : Bool, (if f then x.1 else x.2) ≠ (if f then y.1 else y.2) := by
      by_cases h1 : x.1 = y.1
      · refine ⟨false, ?_⟩
        simp only [Bool.false_eq_true, ite_false]
        exact fun h2 => hxy (Prod.ext h1 h2)
      · exact ⟨true, by simpa using h1⟩
    set v : Mask k := (if f then x.1 else x.2) - (if f then y.1 else y.2) with hv
    have hv0 : v ≠ 0 := sub_ne_zero.2 hf
    have hcount := card_dot_eq_one v hv0
    have hsrc : ((univ.filter (fun a : Mask k => a ⬝ᵥ v = 1)) ×ˢ (univ : Finset (ZMod 2))).card
        = (univ.filter (fun a : Mask k => a ⬝ᵥ v = 1)).card * 2 := by
      rw [card_product]
      have h2 : (univ : Finset (ZMod 2)).card = 2 := by rw [card_univ, ZMod.card]
      rw [h2]
    have hle : ((univ.filter (fun a : Mask k => a ⬝ᵥ v = 1)) ×ˢ (univ : Finset (ZMod 2))).card
        ≤ ((parityActions k).filter
          (fun p => ¬ (parityMem p (some x) ↔ parityMem p (some y)))).card := by
      apply card_le_card_of_injOn
        (fun q : Mask k × ZMod 2 => ((f, q.1, q.2) : ParityIndex k))
      · rintro ⟨a, b⟩ hq
        have ha : a ⬝ᵥ v = 1 := (mem_filter.1 (mem_product.1 (mem_coe.1 hq)).1).2
        have ha0 : a ≠ 0 := by
          rintro rfl
          rw [zero_dotProduct] at ha
          exact absurd ha (by decide)
        have ha2 : a ⬝ᵥ (if f then x.1 else x.2) - a ⬝ᵥ (if f then y.1 else y.2) = 1 := by
          rw [← dotProduct_sub]
          exact ha
        refine mem_coe.2 (mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, ha0⟩, ?_⟩)
        intro hiff
        exact (by decide : ∀ p q b : ZMod 2, p - q = 1 → ¬ (p = b ↔ q = b)) _ _ b ha2 hiff
      · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.2.1 h.2.2
    omega

/-- **Every-layout run lower bound.**  For every ordering `π` of the `r^2 + 1` terminals of
the parity grid, the `d` parity supports have at least `r^3 / 2` contiguous runs in total
(the manuscript states the weaker `r (r^2 - 1) / 2`). -/
theorem parityGrid_runs_lower {k : ℕ} (hk : 1 ≤ k)
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1)) :
    2 ^ k * 2 ^ k * 2 ^ k
      ≤ 2 * ∑ p ∈ parityActions k, runs (layoutPos π (paritySupp p)) := by
  have := total_runs_lower π (parityActions k) (fun p => paritySupp p) (2 ^ k) (by
    intro t t' htt'
    have := parity_separation hk t t' htt'
    simpa [paritySupp] using this)
  simpa using this

/-- **Every-layout dyadic cover lower bound** (`thm:coded-covers`, `thm:coded-main`:
the `Ω(r^3)` half).  For `r = 2^k ≥ 2`, every terminal ordering `π` of the parity grid and
every choice of dyadic covers `C p` of the `d = 4(r-1)` parity root supports under `π`,
the number of root-to-block incidences `Σ_p |C p|` is at least `r^3 / 2`.  Sharing of block
gates across actions does not reduce this count, since it counts pairs (action, block). -/
theorem parityGrid_cover_lower {k : ℕ} (hk : 1 ≤ k)
    (π : GridTerminal k ≃ Fin (2 ^ k * 2 ^ k + 1))
    (C : ParityIndex k → Finset (Finset ℕ))
    (hC : ∀ p ∈ parityActions k, IsDyadicCover (C p) (layoutPos π (paritySupp p))) :
    2 ^ k * 2 ^ k * 2 ^ k ≤ 2 * ∑ p ∈ parityActions k, (C p).card := by
  refine (parityGrid_runs_lower hk π).trans (Nat.mul_le_mul_left 2 ?_)
  exact sum_le_sum (fun p hp => runs_le_card_of_cover (hC p hp))

/-- Selection inequality of Step 3 of the proof of `thm:coded-covers`: a losing action with
empirical mean at most `0.03` and count `N` can have index at least `0.98` under
exploration constant `2` only if `N ≤ (2/0.95)^2 log(1+t)`; here `L = log(1+t)`. -/
lemma losing_action_count_bound {N L : ℝ} (hN : 0 < N) (hL : 0 ≤ L)
    (h : 0.98 ≤ 0.03 + 2 * Real.sqrt (L / N)) : N ≤ (2 / 0.95) ^ 2 * L := by
  have hs : (0.475 : ℝ) ≤ Real.sqrt (L / N) := by linarith
  have hsq := Real.sq_sqrt (div_nonneg hL hN.le)
  have h1 : (0.475 : ℝ) ^ 2 ≤ L / N := by
    rw [← hsq]
    exact pow_le_pow_left₀ (by norm_num) hs 2
  have h2 : (0.475 : ℝ) ^ 2 * N ≤ L := (le_div_iff₀ hN).1 h1
  have e : ((2 : ℝ) / 0.95) ^ 2 * 0.475 ^ 2 = 1 := by norm_num
  calc N = ((2 : ℝ) / 0.95) ^ 2 * 0.475 ^ 2 * N := by rw [e, one_mul]
    _ = (2 / 0.95) ^ 2 * (0.475 ^ 2 * N) := by ring
    _ ≤ (2 / 0.95) ^ 2 * L := by gcongr

end ParityGrid

end Representation
end JointRootCert
