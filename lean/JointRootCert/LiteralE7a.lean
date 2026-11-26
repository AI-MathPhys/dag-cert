/-
Appendix E, second-round gaps (part 2): `eq:ram-work-bounds` (in the proof of
`prop:uct-coupling`, "Safe permanent retirement") with linear initialisation and
`O(log (2 + D))` per delivery.

1. **Bottom-up heap construction** in the cost model of `HeapImpl.lean`
   (`HeapB.heapify`): write the `m` entries into the array (`m + 1` units), then sift down
   from positions `m-1, …, 0` with the implemented `HeapImpl.siftDown`.
   `HeapB.rep_heapify`: the result represents the key table, at computed cost at most
   `4 m + 1`.  The sift-down from position `j` costs at most `⌊log₂ (m/(j+1))⌋ + 2`
   (`siftDown_cost_height`), and `Σ_{j<m} ⌊log₂ (m/(j+1))⌋ ≤ m` (`sum_log_div_le`).
   `initPassB` is `EngineFinal.initPassH` with every gate heap built by `heapify`; it
   represents the same abstract state (`initPassB_sim`) at cost at most
   `Σ_{g ∈ order} (4 deg g + 2)`.

2. **A wave scheduler without levels** (`waveD`).  The changed gates are kept on a stack.
   Popping a gate `g` delivers its value to every parent `p` (one `HeapImpl.updateKey` in
   the heap of `p`, one comparison of `findMax` with the stored value of `p`); if the
   value of `p` changes, it is stored and `p` is pushed (1 unit).  No order among pending
   gates is needed: for a single changed terminal `x`, either every changed gate moves up
   to the common value `y` (`y ≥ old x`) or every changed gate had the old value of `x`
   (`y ≤ old x`) (`incFact`, `decFact`, `dir_of_wave`), and from this each gate's value
   changes at most once and, when it changes, to its final value (`dlvOne_spec`).
   `waveD_spec`: from an implemented state representing a state satisfying the engine
   invariant, `waveD` ends in an implemented state representing `CostEngines.wave` (so all
   correctness statements about `wave` apply), its computed cost is at most
   `3 + Σ_{changed g} dcost g + 2 · (deliveries)` and at least the number of deliveries.
   There is no term in `L`.

3. **Assembly** (`ram_work_bounds_display`) for the trajectories `LiteralE4.Traj` of
   `LiteralE4.ram_work_bounds_literal`, with initialisation `initPassB`, Graph-Eager
   `runED` and Graph-Selective `runSD` (both with `waveD`):
   `initW ≤ 4 (|V| + 2 |E|)`,
   `T + S₀ ≤ W_eager ≤ initW + samp + 6T + 2QK + (⌈log₂ D⌉ + 5) S₀`,
   `T + S ≤ W_live ≤ initW + samp + 6T + 8QK + 2(⌈log₂ D⌉ + 6) S + 2(2⌈log₂ D⌉ + 4) R
      + 4 (|V| + |E|)`,
   and both engines return the same leader and stopping bit at every time.  This is the
   display `eq:ram-work-bounds` with `T` read as the sampler work `samp` (between `T` and
   `T (L + 1)(D + 1)`, `LiteralE4.Traj.samp_bounds`), the only remaining difference.

Unit charges (by definition): `m + 1` for writing an array of `m` entries; 1 per
comparison of a gate value with `findMax`, per stack push, per stack pop and for the final
empty-stack test; everything in `HeapImpl` is computed.
-/
import JointRootCert.LiteralE4

namespace JointRootCert
namespace LiteralE7a

open Finset CostEngines DagRetire EngineFinal RetireFinal
open HeapImpl (Heap HEState SimE Rep findMax updateKey targetH par Ord swapK siftDown bigChild
  bigChild_spec par_lt par_eq_iff fuel_dn)

/-! ## 1. Bottom-up heap construction -/

namespace HeapB

section Order

variable {α : Type*} [LinearOrder α]

/-- Heap order on the subtrees rooted at positions `≥ r`. -/
def OrdR (n : ℕ) (k : ℕ → α) (r : ℕ) : Prop :=
  ∀ i, 0 < i → i < n → r ≤ par i → k i ≤ k (par i)

/-- `OrdR` except possibly between `j` and its children. -/
def OrdDnR (n : ℕ) (k : ℕ → α) (r j : ℕ) : Prop :=
  (∀ i, 0 < i → i < n → r ≤ par i → par i ≠ j → k i ≤ k (par i)) ∧
  (∀ i, 0 < i → i < n → par i = j → 0 < j → r ≤ par j → k i ≤ k (par j))

lemma ordDnR_done {n : ℕ} {k : ℕ → α} {r j : ℕ} (h : OrdDnR n k r j)
    (hj : ∀ i, 0 < i → i < n → par i = j → k i ≤ k j) : OrdR n k r := by
  intro i hi hin hr
  by_cases hp : par i = j
  · rw [hp]; exact hj i hi hin hp
  · exact h.1 i hi hin hr hp

lemma ordDnR_swap {n : ℕ} {k : ℕ → α} {r j m : ℕ} (h : OrdDnR n k r j) (hrj : r ≤ j)
    (hm : 0 < m) (hmn : m < n) (hpm : par m = j) (hlt : k j < k m)
    (hbig : ∀ i, 0 < i → i < n → par i = j → k i ≤ k m) : OrdDnR n (swapK k j m) r m := by
  have hjm : j < m := hpm ▸ par_lt hm
  have e1 : swapK k j m j = k m := by simp [swapK]
  have e2 : swapK k j m m = k j := by
    unfold swapK; rw [ite_eq_right (by omega), ite_eq_left rfl]
  have e3 : ∀ i, i ≠ j → i ≠ m → swapK k j m i = k i := by
    intro i h1 h2; unfold swapK; rw [ite_eq_right h1, ite_eq_right h2]
  constructor
  · intro i hi hin hr hne
    by_cases him : i = m
    · subst him
      rw [e2, hpm, e1]; exact hlt.le
    · by_cases hij : i = j
      · subst hij
        have hpi := par_lt hi
        rw [e1, e3 _ (by omega) (by omega)]
        exact h.2 m hm hmn hpm hi hr
      · rw [e3 i hij him]
        by_cases hp : par i = j
        · rw [hp, e1]; exact hbig i hi hin hp
        · rw [e3 _ hp hne]
          exact h.1 i hi hin hr hp
  · intro i hi hin hp _ _
    have hij : i ≠ j := by have := par_lt hi; omega
    have him : i ≠ m := by have := par_lt hi; omega
    rw [e3 i hij him, hpm, e1]
    have := h.1 i hi hin (by omega) (by omega)
    rwa [hp] at this

end Order

section Ops

variable {ι α : Type*} [DecidableEq ι] [LinearOrder α]

lemma siftDown_n : ∀ (d : ℕ) (H : Heap ι α) (j : ℕ), (siftDown d H j).1.n = H.n := by
  intro d
  induction d with
  | zero => intro H j; rfl
  | succ d ih =>
    intro H j
    rw [siftDown]
    split_ifs
    · exact ih _ _
    · rfl

/-- **Sift-down within the region `≥ r`.** -/
theorem siftDownR_spec : ∀ (d : ℕ) (H : Heap ι α) (r j : ℕ), H.PosOK → OrdDnR H.n H.ky r j →
    r ≤ j → j < H.n → H.n ≤ (j + 1) * 2 ^ d →
    (siftDown d H j).1.PosOK ∧ OrdR (siftDown d H j).1.n (siftDown d H j).1.ky r ∧
      (siftDown d H j).1.n = H.n ∧ ∀ h, (siftDown d H j).1.lookup h = H.lookup h := by
  intro d
  induction d with
  | zero =>
    intro H r j hP hO hrj hj hd
    refine ⟨hP, ordDnR_done hO ?_, rfl, fun _ => rfl⟩
    intro i hi hin hp
    exfalso
    have hin' : i < H.n := hin
    have := (par_eq_iff hi).1 hp
    simp at hd
    omega
  | succ d ih =>
    intro H r j hP hO hrj hj hd
    rw [siftDown]
    by_cases hc : 2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j)
    · rw [ite_eq_left hc]
      obtain ⟨hm0, hmn, hpm, hbig⟩ := bigChild_spec H j hc.1
      have hjm : j < bigChild H j := by
        have := par_lt hm0
        rw [hpm] at this
        exact this
      have hP' := Heap.swap_posOK hP hj hmn (by omega)
      have hfuel : H.n ≤ (bigChild H j + 1) * 2 ^ d := by
        have h1 : 2 * (j + 1) ≤ bigChild H j + 1 := by
          have := (par_eq_iff hm0).1 hpm; omega
        calc H.n ≤ (j + 1) * 2 ^ (d + 1) := hd
          _ = 2 * (j + 1) * 2 ^ d := by ring
          _ ≤ (bigChild H j + 1) * 2 ^ d := Nat.mul_le_mul_right _ h1
      obtain ⟨h1, h2, h3, h4⟩ := ih (H.swap j (bigChild H j)) r (bigChild H j) hP'
        (ordDnR_swap hO hrj hm0 hmn hpm hc.2 hbig) (by omega) hmn hfuel
      refine ⟨h1, h2, h3, fun h => ?_⟩
      rw [h4 h]
      exact Heap.swap_lookup hP hj hmn (by omega) h
    · rw [ite_eq_right hc]
      refine ⟨hP, ordDnR_done hO ?_, rfl, fun _ => rfl⟩
      intro i hi hin hp
      have hin' : i < H.n := hin
      have hl : 2 * j + 1 < H.n := by
        have := (par_eq_iff hi).1 hp; omega
      obtain ⟨_, _, _, hbig⟩ := bigChild_spec H j hl
      refine (hbig i hi hin' hp).trans ?_
      by_contra hlt
      exact hc ⟨hl, lt_of_not_ge hlt⟩

/-- **Cost of a sift-down by height**: if `n ≤ (j + 1) 2^k` then sifting down from `j`
costs at most `k + 1`, whatever the fuel. -/
theorem siftDown_cost_height : ∀ (d : ℕ) (H : Heap ι α) (j k : ℕ), H.n ≤ (j + 1) * 2 ^ k →
    (siftDown d H j).2 ≤ k + 1 := by
  intro d
  induction d with
  | zero => intro H j k _; show 1 ≤ k + 1; omega
  | succ d ih =>
    intro H j k hk
    rw [siftDown]
    by_cases hc : 2 * j + 1 < H.n ∧ H.ky j < H.ky (bigChild H j)
    · rw [ite_eq_left hc]
      obtain ⟨hm0, _, hpm, _⟩ := bigChild_spec H j hc.1
      have h1 : 2 * (j + 1) ≤ bigChild H j + 1 := by
        have := (par_eq_iff hm0).1 hpm; omega
      cases k with
      | zero => simp at hk; omega
      | succ k =>
        have hk' : (H.swap j (bigChild H j)).n ≤ (bigChild H j + 1) * 2 ^ k := by
          show H.n ≤ _
          calc H.n ≤ (j + 1) * 2 ^ (k + 1) := hk
            _ = 2 * (j + 1) * 2 ^ k := by ring
            _ ≤ (bigChild H j + 1) * 2 ^ k := Nat.mul_le_mul_right _ h1
        have := ih (H.swap j (bigChild H j)) (bigChild H j) k hk'
        show _ + 1 ≤ k + 1 + 1
        omega
    · rw [ite_eq_right hc]
      show 1 ≤ k + 1
      omega

lemma n_le_height (n j : ℕ) : n ≤ (j + 1) * 2 ^ (Nat.log 2 (n / (j + 1)) + 1) := by
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n / (j + 1))
  have h2 := Nat.lt_mul_div_succ n (Nat.succ_pos j)
  have h3 : n / (j + 1) + 1 ≤ 2 ^ (Nat.log 2 (n / (j + 1)) + 1) := h1
  calc n ≤ (j + 1) * (n / (j + 1) + 1) := h2.le
    _ ≤ (j + 1) * 2 ^ (Nat.log 2 (n / (j + 1)) + 1) := Nat.mul_le_mul_left _ h3

/-- `Σ_{j < n} ⌊log₂ (n / (j + 1))⌋ ≤ n`. -/
theorem sum_log_div_le : ∀ n : ℕ, ∑ j ∈ range n, Nat.log 2 (n / (j + 1)) ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hsplit := Finset.sum_range_add_sum_Ico (fun j => Nat.log 2 (n / (j + 1)))
        (Nat.div_le_self n 2)
      have hhi : ∑ j ∈ Ico (n / 2) n, Nat.log 2 (n / (j + 1)) = 0 := by
        apply sum_eq_zero
        intro j hj
        rw [mem_Ico] at hj
        apply Nat.log_of_lt
        rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos j)]
        omega
      have hlo : ∑ j ∈ range (n / 2), Nat.log 2 (n / (j + 1))
          = ∑ j ∈ range (n / 2), (Nat.log 2 (n / 2 / (j + 1)) + 1) := by
        apply sum_congr rfl
        intro j hj
        rw [mem_range] at hj
        rw [Nat.log_of_one_lt_of_le (by norm_num : 1 < 2)]
        · rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
        · rw [Nat.le_div_iff_mul_le (Nat.succ_pos j)]
          omega
      rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one] at hlo
      have := ih (n / 2) (by omega)
      omega

/-- Sift down from positions `j - 1, …, 0`. -/
def heapLoop : ℕ → Heap ι α → Heap ι α × ℕ
  | 0, H => (H, 0)
  | j + 1, H => ((heapLoop j (siftDown (Nat.clog 2 H.n) H j).1).1,
      (siftDown (Nat.clog 2 H.n) H j).2 + (heapLoop j (siftDown (Nat.clog 2 H.n) H j).1).2)

theorem heapLoop_spec : ∀ (j : ℕ) (H : Heap ι α), H.PosOK → OrdR H.n H.ky j → j ≤ H.n →
    (heapLoop j H).1.Inv ∧ (heapLoop j H).1.n = H.n ∧
      (∀ h, (heapLoop j H).1.lookup h = H.lookup h) ∧
      (heapLoop j H).2 ≤ ∑ i ∈ range j, (Nat.log 2 (H.n / (i + 1)) + 2) := by
  intro j
  induction j with
  | zero =>
    intro H hP hO _
    refine ⟨⟨hP, fun i hi hin => hO i hi hin (Nat.zero_le _)⟩, rfl, fun _ => rfl, by simp [heapLoop]⟩
  | succ j ih =>
    intro H hP hO hj
    have hD : OrdDnR H.n H.ky j j := by
      refine ⟨fun i hi hin hr hne => hO i hi hin (by omega), ?_⟩
      intro i _ _ _ hj0 hr
      have := par_lt hj0
      omega
    obtain ⟨a1, a2, a3, a4⟩ := siftDownR_spec (Nat.clog 2 H.n) H j j hP hD le_rfl (by omega)
      (fuel_dn j)
    rw [a3] at a2
    obtain ⟨b1, b2, b3, b4⟩ := ih (siftDown (Nat.clog 2 H.n) H j).1 a1 (by rw [a3]; exact a2)
      (by rw [a3]; omega)
    rw [a3] at b2 b4
    have hc := siftDown_cost_height (Nat.clog 2 H.n) H j _ (n_le_height H.n j)
    refine ⟨b1, b2, fun h => by show (heapLoop j _).1.lookup h = _; rw [b3 h, a4 h], ?_⟩
    show (siftDown (Nat.clog 2 H.n) H j).2 + (heapLoop j _).2 ≤ _
    rw [sum_range_succ]
    omega

variable [Inhabited ι]

/-- The array of a key table: `m` entries written in list order. -/
def ofKeys (cs : List ι) (k : ι → α) : Heap ι α :=
  ⟨cs.length, fun i => cs.getD i default, fun i => k (cs.getD i default),
    fun h => if h ∈ cs then some (cs.idxOf h) else none⟩

/-- **Bottom-up heap construction**: write the array (`m + 1` units), then `heapLoop m`. -/
def heapify (cs : List ι) (k : ι → α) : Heap ι α × ℕ :=
  ((heapLoop cs.length (ofKeys cs k)).1, cs.length + 1 + (heapLoop cs.length (ofKeys cs k)).2)

omit [LinearOrder α] in
lemma ofKeys_posOK (cs : List ι) (hnd : cs.Nodup) (k : ι → α) : (ofKeys cs k).PosOK := by
  constructor
  · intro i hi
    have hi' : i < cs.length := hi
    show (if cs.getD i default ∈ cs then some (cs.idxOf (cs.getD i default)) else none) = some i
    rw [List.getD_eq_getElem _ _ hi', ite_eq_left (List.getElem_mem hi'), hnd.idxOf_getElem i hi']
  · intro h i hp
    change (if h ∈ cs then some (cs.idxOf h) else none) = some i at hp
    by_cases hm : h ∈ cs
    · rw [ite_eq_left hm] at hp
      have e : cs.idxOf h = i := Option.some.inj hp
      have hlt : cs.idxOf h < cs.length := List.idxOf_lt_length_iff.2 hm
      refine ⟨by rw [← e]; exact hlt, ?_⟩
      show cs.getD i default = h
      rw [← e, List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]
    · rw [ite_eq_right hm] at hp
      exact absurd hp (by simp)

omit [LinearOrder α] in
lemma ofKeys_lookup (cs : List ι) (k : ι → α) (h : ι) :
    (ofKeys cs k).lookup h = if h ∈ cs.toFinset then some (k h) else none := by
  show Option.map (fun i => k (cs.getD i default))
    (if h ∈ cs then some (cs.idxOf h) else none) = _
  by_cases hm : h ∈ cs
  · have hlt : cs.idxOf h < cs.length := List.idxOf_lt_length_iff.2 hm
    rw [ite_eq_left hm, ite_eq_left (List.mem_toFinset.2 hm), Option.map_some,
      List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]
  · rw [ite_eq_right hm, ite_eq_right (fun h' => hm (List.mem_toFinset.1 h'))]
    rfl

/-- **Correctness and linear cost of bottom-up heap construction.**  For a duplicate-free
list of `m` handles, `heapify` returns a heap representing the key table at computed cost
at most `4 m + 1`. -/
theorem rep_heapify (cs : List ι) (hnd : cs.Nodup) (k : ι → α) :
    Rep (heapify cs k).1 cs.toFinset k cs.length ∧ (heapify cs k).2 ≤ 4 * cs.length + 1 := by
  have hP := ofKeys_posOK cs hnd k
  have hO : OrdR (ofKeys cs k).n (ofKeys cs k).ky cs.length := by
    intro i hi hin hr
    have hin' : i < cs.length := hin
    have := par_lt hi
    omega
  obtain ⟨h1, h2, h3, h4⟩ := heapLoop_spec cs.length (ofKeys cs k) hP hO le_rfl
  have hn : (ofKeys cs k).n = cs.length := rfl
  rw [hn] at h2 h4
  refine ⟨⟨h1, h2.le, fun h => by
    show (heapLoop cs.length (ofKeys cs k)).1.lookup h = _
    rw [h3 h, ofKeys_lookup]⟩, ?_⟩
  have hs := sum_log_div_le cs.length
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul] at h4
  show cs.length + 1 + (heapLoop cs.length (ofKeys cs k)).2 ≤ _
  omega

end Ops

end HeapB

/-! ### Initialisation with bottom-up heap construction -/

section InitB

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- Initialise one internal gate: build its heap from the stored values of its children
by `heapify`, then read the heap root into the gate (1 unit). -/
def initGateB (G : Dag) (g : ℕ) (s : HEState α) : HEState α × ℕ :=
  (⟨fun g' => if g' = g then findMax (HeapB.heapify (G.children g) s.val).1 else s.val g',
    Function.update s.hp g (HeapB.heapify (G.children g) s.val).1⟩,
   (HeapB.heapify (G.children g) s.val).2 + 1)

/-- **Initialisation pass with bottom-up heap construction.** -/
def initPassB (G : Dag) : List ℕ → HEState α → HEState α × ℕ
  | [], s => (s, 0)
  | g :: rest, s =>
    ((initPassB G rest (initGateB G g s).1).1,
     (initGateB G g s).2 + (initPassB G rest (initGateB G g s).1).2)

lemma initGateB_sim {G : Dag} {g : ℕ} {rest : List ℕ} {hs : HEState α} {s : EState α}
    (hnd : (G.children g).Nodup) (h : PSim G (g :: rest) hs s) :
    PSim G rest (initGateB G g hs).1 (initGate G g s).1 ∧
    (initGateB G g hs).2 ≤ 4 * (G.children g).length + 2 := by
  obtain ⟨s1, s2, s3, s4, _⟩ := initGate_spec G g s
  obtain ⟨rb, rc⟩ := HeapB.rep_heapify (G.children g) hnd hs.val
  have hv := h.val
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · funext g'
    show (if g' = g then findMax _ else hs.val g') = (initGate G g s).1.val g'
    by_cases e : g' = g
    · rw [ite_eq_left e, e, rb.findMax, s4, HeapImpl.heapMax_eq_sup]
      apply Finset.sup_congr rfl
      intro c hc
      rw [s3 c (List.mem_toFinset.1 hc), hv]
    · rw [ite_eq_right e, s1 g' e, hv]
  · intro p hp
    show Rep (Function.update hs.hp g _ p) _ _ _
    by_cases e : p = g
    · rw [e, Function.update_self]
      refine rb.congr (fun c hc => ?_)
      rw [s3 c (List.mem_toFinset.1 hc), hv]
    · rw [Function.update_of_ne e]
      have hp' : p ∉ g :: rest := fun hm => by
        rcases List.mem_cons.1 hm with hm | hm
        · exact e hm
        · exact hp hm
      exact (h.hp p hp').congr (fun c _ => (s2 p c e).symm)
  · show _ + 1 ≤ _
    omega

lemma initPassB_loop {G : Dag} : ∀ (rest : List ℕ) (hs : HEState α) (s : EState α),
    (∀ g ∈ rest, (G.children g).Nodup) → PSim G rest hs s →
    SimE G (initPassB G rest hs).1 (initPass G rest s).1 ∧
    (initPassB G rest hs).2 ≤ (rest.map (fun g => 4 * (G.children g).length + 2)).sum := by
  intro rest
  induction rest with
  | nil => intro hs s _ h; exact ⟨⟨h.val, fun p => h.hp p List.not_mem_nil⟩, le_rfl⟩
  | cons g rest ih =>
    intro hs s hnd h
    obtain ⟨a1, a2⟩ := initGateB_sim (hnd g List.mem_cons_self) h
    obtain ⟨b1, b2⟩ := ih _ _ (fun g' hg' => hnd g' (List.mem_cons_of_mem _ hg')) a1
    refine ⟨b1, ?_⟩
    show (initGateB G g hs).2 + (initPassB G rest (initGateB G g hs).1).2 ≤ _
    rw [List.map_cons, List.sum_cons]
    omega

/-- **The initialisation pass with bottom-up heaps.**  Starting from empty heaps, with the
child lists free of repetitions and every internal gate listed in `order`, `initPassB`
represents the state of `DagRetire.initPass` (so `initPass_spec` applies) at computed
cost at most `Σ_{g ∈ order} (4 deg g + 2)`. -/
theorem initPassB_sim {G : Dag} (order : List ℕ) (hs : HEState α) (s : EState α)
    (hnd : ∀ g, (G.children g).Nodup) (hall : ∀ g, G.children g ≠ [] → g ∈ order)
    (hval : hs.val = s.val) (hemp : ∀ p, hs.hp p = Heap.empty) :
    SimE G (initPassB G order hs).1 (initPass G order s).1 ∧
    (initPassB G order hs).2 ≤ (order.map (fun g => 4 * (G.children g).length + 2)).sum := by
  apply initPassB_loop order hs s (fun g _ => hnd g)
  refine ⟨hval, fun p hp => ?_⟩
  have hc : G.children p = [] := by
    by_contra hne
    exact hp (hall p hne)
  rw [hemp p, hc]
  exact ⟨Heap.empty_inv, le_rfl, fun _ => rfl⟩

end InitB

/-! ## 2. A wave scheduler without levels -/

section Facts

variable {α : Type*} [LinearOrder α] [OrderBot α]

lemma heapMax_ne_exists {cs : List ℕ} {k k' : ℕ → α} (h : heapMax cs k' ≠ heapMax cs k) :
    ∃ c ∈ cs, k' c ≠ k c := by
  by_contra hc
  apply h
  apply heapMax_congr
  intro c hcs
  by_contra hne
  exact hc ⟨c, hcs, hne⟩

/-- **MAX under upward moves to a common value.**  If every key either keeps its old value
or moves up to `b`, the maximum either keeps its old value or moves up to `b`. -/
lemma incFact {cs : List ℕ} {o κ : ℕ → α} {b : α}
    (h : ∀ c ∈ cs, o c ≤ κ c ∧ (κ c ≠ o c → κ c = b)) :
    heapMax cs o ≤ heapMax cs κ ∧ (heapMax cs κ ≠ heapMax cs o → heapMax cs κ = b) := by
  have hle : heapMax cs o ≤ heapMax cs κ := heapMax_mono (fun c hc => (h c hc).1)
  refine ⟨hle, fun hne => ?_⟩
  have hlt : heapMax cs o < heapMax cs κ := lt_of_le_of_ne hle (Ne.symm hne)
  have hup : heapMax cs κ ≤ max (heapMax cs o) b := by
    apply heapMax_le
    intro c hc
    by_cases e : κ c = o c
    · rw [e]
      exact (le_heapMax o hc).trans (le_max_left _ _)
    · rw [(h c hc).2 e]
      exact le_max_right _ _
  obtain ⟨c, hc, hne'⟩ := heapMax_ne_exists hne
  have hb : b ≤ heapMax cs κ := by
    rw [← (h c hc).2 hne']
    exact le_heapMax κ hc
  rcases le_total (heapMax cs o) b with hob | hbo
  · rw [max_eq_right hob] at hup
    exact le_antisymm hup hb
  · rw [max_eq_left hbo] at hup
    exact absurd hup (not_le.2 hlt)

/-- **MAX under downward moves from a common value.**  If every key either keeps its old
value or moves down from the old value `a`, then the maximum either keeps its old value or
its old value was `a`. -/
lemma decFact {cs : List ℕ} {o κ : ℕ → α} {a : α}
    (h : ∀ c ∈ cs, κ c ≤ o c ∧ (κ c ≠ o c → o c = a)) :
    heapMax cs κ ≤ heapMax cs o ∧ (heapMax cs κ ≠ heapMax cs o → heapMax cs o = a) := by
  have hle : heapMax cs κ ≤ heapMax cs o := heapMax_mono (fun c hc => (h c hc).1)
  refine ⟨hle, fun hne => ?_⟩
  have hlt : heapMax cs κ < heapMax cs o := lt_of_le_of_ne hle hne
  have hup : heapMax cs o ≤ max (heapMax cs κ) a := by
    apply heapMax_le
    intro c hc
    by_cases e : κ c = o c
    · rw [← e]
      exact (le_heapMax κ hc).trans (le_max_left _ _)
    · rw [(h c hc).2 e]
      exact le_max_right _ _
  obtain ⟨c, hc, hne'⟩ := heapMax_ne_exists hne
  have ha : a ≤ heapMax cs o := by
    rw [← (h c hc).2 hne']
    exact le_heapMax o hc
  rcases le_total (heapMax cs κ) a with hka | hak
  · rw [max_eq_right hka] at hup
    exact le_antisymm hup ha
  · rw [max_eq_left hak] at hup
    exact absurd hup (not_le.2 hlt)

/-- Every gate either keeps its value or moves up to `b`. -/
def DirInc (o f : ℕ → α) (b : α) : Prop := ∀ g, o g ≤ f g ∧ (f g ≠ o g → f g = b)

/-- Every gate either keeps its value or moves down, and then its old value was `a`. -/
def DirDec (o f : ℕ → α) (a : α) : Prop := ∀ g, f g ≤ o g ∧ (f g ≠ o g → o g = a)

/-- The direction of a single-terminal change. -/
def Dir (o f : ℕ → α) : Prop := (∃ b, DirInc o f b) ∨ (∃ a, DirDec o f a)

theorem dirInc_of_leaves {G : Dag} (hG : G.WF) {o f : ℕ → α} (ho : Exact G o) (hf : Exact G f)
    {b : α} (hl : ∀ g, G.children g = [] → o g ≤ f g ∧ (f g ≠ o g → f g = b)) :
    DirInc o f b := by
  have key : ∀ n, ∀ g, G.level g < n → o g ≤ f g ∧ (f g ≠ o g → f g = b) := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg
      by_cases hc : G.children g = []
      · exact hl g hc
      · rw [ho g hc, hf g hc]
        exact incFact (fun c hcm => ih c (by have := hG.level_lt g c hcm; omega))
  exact fun g => key (G.level g + 1) g (Nat.lt_succ_self _)

theorem dirDec_of_leaves {G : Dag} (hG : G.WF) {o f : ℕ → α} (ho : Exact G o) (hf : Exact G f)
    {a : α} (hl : ∀ g, G.children g = [] → f g ≤ o g ∧ (f g ≠ o g → o g = a)) :
    DirDec o f a := by
  have key : ∀ n, ∀ g, G.level g < n → f g ≤ o g ∧ (f g ≠ o g → o g = a) := by
    intro n
    induction n with
    | zero => intro g hg; omega
    | succ n ih =>
      intro g hg
      by_cases hc : G.children g = []
      · exact hl g hc
      · rw [ho g hc, hf g hc]
        exact decFact (fun c hcm => ih c (by have := hG.level_lt g c hcm; omega))
  exact fun g => key (G.level g + 1) g (Nat.lt_succ_self _)

/-- **A wave has a direction.** -/
theorem dir_of_wave {G : Dag} (hG : G.WF) (x : ℕ) (y : α) (s0 : EState α) (hx : x < G.N)
    (h0 : Inv G s0) : Dir s0.val (wave G x y s0).1.val := by
  obtain ⟨w1, w2, w3, _⟩ := wave_spec hG x y s0 hx h0
  have ho := inv_exact h0
  have hf := inv_exact w1
  by_cases hxl : G.children x = []
  · rcases le_total (s0.val x) y with hle | hle
    · left
      refine ⟨y, dirInc_of_leaves hG ho hf (fun g hg => ?_)⟩
      by_cases e : g = x
      · subst e
        rw [w2 hg]
        exact ⟨hle, fun _ => rfl⟩
      · rw [w3 g hg e]
        exact ⟨le_rfl, fun h => absurd rfl h⟩
    · right
      refine ⟨s0.val x, dirDec_of_leaves hG ho hf (fun g hg => ?_)⟩
      by_cases e : g = x
      · subst e
        rw [w2 hg]
        exact ⟨hle, fun _ => rfl⟩
      · rw [w3 g hg e]
        exact ⟨le_rfl, fun h => absurd rfl h⟩
  · left
    refine ⟨y, dirInc_of_leaves hG ho hf (fun g hg => ?_)⟩
    have hgx : g ≠ x := fun e => hxl (e ▸ hg)
    rw [w3 g hg hgx]
    exact ⟨le_rfl, fun h => absurd rfl h⟩

/-- **The delivery core.**  At a gate `p` with child list `cs`, let the keys `k` (before)
and `k'` (after a delivery from child `g`) each hold, for every child, its old or its final
value, and let `k'` differ from `k` only at children whose key moved from old to final.  If
the maximum changes, then before the delivery it was the old value of `p` and after it is
the final value of `p`. -/
theorem deliver_core {cs : List ℕ} {o f k k' : ℕ → α} {p : ℕ} (hD : Dir o f)
    (hop : o p = heapMax cs o) (hfp : f p = heapMax cs f)
    (hk : ∀ c ∈ cs, k c = o c ∨ k c = f c) (hk' : ∀ c ∈ cs, k' c = o c ∨ k' c = f c)
    (hkk : ∀ c ∈ cs, k' c = k c ∨ (k c = o c ∧ k' c = f c))
    (hne : heapMax cs k' ≠ heapMax cs k) :
    heapMax cs k = o p ∧ heapMax cs k' = f p := by
  rcases hD with ⟨b, hI⟩ | ⟨a, hDd⟩
  · have hκ : ∀ κ : ℕ → α, (∀ c ∈ cs, κ c = o c ∨ κ c = f c) →
        ∀ c ∈ cs, o c ≤ κ c ∧ (κ c ≠ o c → κ c = b) := by
      intro κ hκ c hc
      rcases hκ c hc with e | e
      · rw [e]; exact ⟨le_rfl, fun h => absurd rfl h⟩
      · rw [e]; exact hI c
    obtain ⟨v1, v2⟩ := incFact (hκ k hk)
    obtain ⟨m1, m2⟩ := incFact (hκ k' hk')
    have hfm : heapMax cs k' ≤ f p := by
      rw [hfp]
      apply heapMax_mono
      intro c hc
      rcases hk' c hc with e | e
      · rw [e]; exact (hI c).1
      · rw [e]
    have hvm : heapMax cs k ≤ heapMax cs k' := by
      apply heapMax_mono
      intro c hc
      rcases hkk c hc with e | ⟨e1, e2⟩
      · rw [e]
      · rw [e1, e2]; exact (hI c).1
    have hfp' := hI p
    rw [← hop] at v1 v2 m1 m2
    have hVO : heapMax cs k = o p := by
      by_contra hVO
      have hV := v2 hVO
      have hMO : heapMax cs k' ≠ o p := by
        intro e
        have : heapMax cs k ≤ o p := e ▸ hvm
        exact hVO (le_antisymm this v1)
      have hM := m2 hMO
      exact hne (hM.trans hV.symm)
    refine ⟨hVO, ?_⟩
    have hMO : heapMax cs k' ≠ o p := by rw [← hVO]; exact hne
    have hM := m2 hMO
    have hfo : f p ≠ o p := by
      intro e
      have : heapMax cs k' ≤ o p := e ▸ hfm
      exact hMO (le_antisymm this m1)
    rw [hM, hfp'.2 hfo]
  · -- the key lemma: a maximum below the old value is the final value
    have hdk : ∀ κ : ℕ → α, (∀ c ∈ cs, κ c = o c ∨ κ c = f c) → heapMax cs κ ≠ o p →
        heapMax cs κ = f p := by
      intro κ hκ hne'
      by_contra hF
      have hlo : f p ≤ heapMax cs κ := by
        rw [hfp]
        apply heapMax_mono
        intro c hc
        rcases hκ c hc with e | e
        · rw [e]; exact (hDd c).1
        · rw [e]
      have hhi : heapMax cs κ ≤ o p := by
        rw [hop]
        apply heapMax_mono
        intro c hc
        rcases hκ c hc with e | e
        · rw [e]
        · rw [e]; exact (hDd c).1
      have hlt : heapMax cs κ < o p := lt_of_le_of_ne hhi hne'
      have hpa : o p = a := (hDd p).2 (ne_of_lt (lt_of_le_of_lt hlo hlt))
      have hex : ∃ c ∈ cs, κ c ≠ f c := by
        by_contra hc
        apply hF
        rw [hfp]
        apply heapMax_congr
        intro c hcs
        by_contra hne
        exact hc ⟨c, hcs, hne⟩
      obtain ⟨c, hc, hcf⟩ := hex
      have hco : κ c = o c := (hκ c hc).resolve_right hcf
      have hca : o c = a := (hDd c).2 (by rw [← hco]; exact Ne.symm hcf)
      have : a ≤ heapMax cs κ := by rw [← hca, ← hco]; exact le_heapMax κ hc
      rw [← hpa] at this
      exact absurd this (not_le.2 hlt)
    have hmk : heapMax cs k' ≤ heapMax cs k := by
      apply heapMax_mono
      intro c hc
      rcases hkk c hc with e | ⟨e1, e2⟩
      · rw [e]
      · rw [e1, e2]; exact (hDd c).1
    have hfk' : f p ≤ heapMax cs k' := by
      rw [hfp]
      apply heapMax_mono
      intro c hc
      rcases hk' c hc with e | e
      · rw [e]; exact (hDd c).1
      · rw [e]
    have hVO : heapMax cs k = o p := by
      by_contra hVO
      have hV := hdk k hk hVO
      exact hne (le_antisymm hmk (by rw [hV]; exact hfk'))
    exact ⟨hVO, hdk k' hk' (by rw [← hVO]; exact hne)⟩

end Facts

section DFS

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **One delivery** of the value `y` of gate `g` to its parent `p`: update the key of `g` in
the heap of `p` (computed cost), compare `findMax` with the stored value of `p` (1 unit);
if it differs, store it and push `p` on the stack (1 unit). -/
def dlvOne (g : ℕ) (y : α) (p : ℕ) (s : HEState α) (st : List ℕ) : HEState α × List ℕ × ℕ :=
  if findMax (updateKey (s.hp p) g y).1 = s.val p then
    (⟨s.val, Function.update s.hp p (updateKey (s.hp p) g y).1⟩, st,
      (updateKey (s.hp p) g y).2 + 1)
  else
    (⟨Function.update s.val p (findMax (updateKey (s.hp p) g y).1),
      Function.update s.hp p (updateKey (s.hp p) g y).1⟩, p :: st,
      (updateKey (s.hp p) g y).2 + 2)

/-- Deliveries of `g` to the parents `ps`. -/
def dlv (g : ℕ) (y : α) : List ℕ → HEState α → List ℕ → HEState α × List ℕ × ℕ
  | [], s, st => (s, st, 0)
  | p :: ps, s, st =>
    ((dlv g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).1,
     (dlv g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).2.1,
     (dlvOne g y p s st).2.2 + (dlv g y ps (dlvOne g y p s st).1 (dlvOne g y p s st).2.1).2.2)

/-- **The stack loop**: pop a gate (1 unit) and deliver its stored value to all its parents;
stop on the empty stack (1 unit). -/
def loopD (G : Dag) : ℕ → HEState α → List ℕ → HEState α × ℕ
  | 0, s, _ => (s, 0)
  | _ + 1, s, [] => (s, 1)
  | f + 1, s, g :: st =>
    ((loopD G f (dlv g (s.val g) (G.parents g) s st).1 (dlv g (s.val g) (G.parents g) s st).2.1).1,
     1 + (dlv g (s.val g) (G.parents g) s st).2.2
       + (loopD G f (dlv g (s.val g) (G.parents g) s st).1
          (dlv g (s.val g) (G.parents g) s st).2.1).2)

/-- **The wave without levels.**  Compare the target value of `x` with its stored value
(1 unit); if it differs, store it and run the stack loop from `[x]`. -/
def waveD (G : Dag) (x : ℕ) (y : α) (s : HEState α) : HEState α × ℕ :=
  if targetH G x y s x = s.val x then (s, 1)
  else ((loopD G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).1,
    1 + (loopD G (G.N + 2) ⟨Function.update s.val x (targetH G x y s x), s.hp⟩ [x]).2)

/-- Invariant of the loop while gate `g` delivers to the parents `ps`: the heaps represent
the ghost keys `k`; internal gates store the maximum of their keys; a key holds the old
value of its child if the child is on the stack or is `g` with the parent still in `ps`,
and the stored value otherwise; stored values are old or final; stacked gates are changed
gates holding their final value; leaves hold their final value. -/
structure DI (G : Dag) (o f : ℕ → α) (g : ℕ) (ps : List ℕ) (s : HEState α) (k : ℕ → ℕ → α)
    (st : List ℕ) : Prop where
  rep : ∀ p, Rep (s.hp p) (G.children p).toFinset (k p) (G.children p).length
  gate : ∀ p, G.children p ≠ [] → s.val p = heapMax (G.children p) (k p)
  key : ∀ p c, c ∈ G.children p → k p c = if c ∈ st ∨ (c = g ∧ p ∈ ps) then o c else s.val c
  val : ∀ q, s.val q = o q ∨ s.val q = f q
  stk : ∀ q ∈ st, s.val q = f q ∧ f q ≠ o q ∧ q < G.N
  nd : st.Nodup
  leaf : ∀ q, G.children q = [] → s.val q = f q

/-- Gates still to change. -/
def Uset (G : Dag) (o f : ℕ → α) (s : HEState α) : Finset ℕ :=
  (range G.N).filter (fun q => s.val q = o q ∧ f q ≠ o q)

/-- Changed gates that have not delivered yet. -/
def Rset (G : Dag) (o f : ℕ → α) (s : HEState α) (st : List ℕ) : Finset ℕ :=
  (range G.N).filter (fun q => f q ≠ o q ∧ (s.val q = o q ∨ q ∈ st))

/-- Charge of a changed gate: `⌈log₂ deg p⌉ + 5` per parent `p`. -/
def wD (G : Dag) (q : ℕ) : ℕ := dcost G q + 2 * (G.parents q).length

lemma DI.reg {G : Dag} {o f : ℕ → α} {g g' : ℕ} {s : HEState α} {k : ℕ → ℕ → α}
    {st : List ℕ} (h : DI G o f g [] s k st) : DI G o f g' [] s k st := by
  refine ⟨h.rep, h.gate, fun p c hc => ?_, h.val, h.stk, h.nd, h.leaf⟩
  rw [h.key p c hc]
  simp

lemma heapMax_of_rep {H : Heap ℕ α} {cs : List ℕ} {k : ℕ → α} {b : ℕ}
    (h : Rep H cs.toFinset k b) : findMax H = heapMax cs k := by
  rw [h.findMax, HeapImpl.heapMax_eq_sup]

variable {G : Dag} {o f : ℕ → α}

/-- **One delivery preserves the invariant.** -/
theorem dlvOne_spec (hG : G.WF) (hD : Dir o f) (ho : Exact G o) (hf : Exact G f) {g p : ℕ}
    {ps : List ℕ} {s : HEState α} {k : ℕ → ℕ → α} {st : List ℕ}
    (h : DI G o f g (p :: ps) s k st) (hg : s.val g = f g) (hgst : g ∉ st)
    (hgp : g ∈ G.children p) (hnd : (p :: ps).Nodup) :
    ∃ k', DI G o f g ps (dlvOne g (s.val g) p s st).1 k' (dlvOne g (s.val g) p s st).2.1 ∧
      (dlvOne g (s.val g) p s st).1.val g = f g ∧ g ∉ (dlvOne g (s.val g) p s st).2.1 ∧
      (dlvOne g (s.val g) p s st).2.1.length + (Uset G o f (dlvOne g (s.val g) p s st).1).card
        = st.length + (Uset G o f s).card ∧
      Rset G o f (dlvOne g (s.val g) p s st).1 (dlvOne g (s.val g) p s st).2.1
        = Rset G o f s st ∧
      (dlvOne g (s.val g) p s st).2.2 + st.length
        ≤ Nat.clog 2 (G.children p).length + 3 + (dlvOne g (s.val g) p s st).2.1.length ∧
      1 ≤ (dlvOne g (s.val g) p s st).2.2 ∧
      (dlvOne g (s.val g) p s st).2.1.length ≤ st.length + 1 := by
  have hpg : p ≠ g := fun e => by
    have := hG.level_lt p g hgp
    rw [e] at this
    exact lt_irrefl _ this
  have hpn : p ∉ ps := (List.nodup_cons.1 hnd).1
  have hpN : p < G.N := hG.parent_lt g p ((hG.parents_iff g p).2 hgp)
  have hpint : G.children p ≠ [] := List.ne_nil_of_mem hgp
  set k' : ℕ → ℕ → α := fun q c => if q = p ∧ c = g then s.val g else k q c with hk'
  have hrepp : Rep (updateKey (s.hp p) g (s.val g)).1 (G.children p).toFinset (k' p)
      (G.children p).length := by
    refine ((h.rep p).update g (s.val g)).congr (fun c _ => ?_)
    simp only [hk', true_and]
  have hM : findMax (updateKey (s.hp p) g (s.val g)).1 = heapMax (G.children p) (k' p) :=
    heapMax_of_rep hrepp
  have hV : s.val p = heapMax (G.children p) (k p) := h.gate p hpint
  have hkof : ∀ q c, c ∈ G.children q → k q c = o c ∨ k q c = f c := by
    intro q c hc
    rw [h.key q c hc]
    split_ifs
    · exact Or.inl rfl
    · exact h.val c
  have hkg : k p g = o g := by
    rw [h.key p g hgp, ite_eq_left (Or.inr ⟨rfl, List.mem_cons_self⟩)]
  have hcost := (h.rep p).updateKey_cost g (s.val g)
  have h1cost := one_le_updateKey (s.hp p) g (s.val g)
  -- the ghost keys after the delivery
  have hkey' : ∀ (val' : ℕ → α) (st' : List ℕ), (∀ c, c ≠ p → val' c = s.val c) →
      (∀ c, c ≠ p → (c ∈ st' ↔ c ∈ st)) → (p ∈ st' → p ∉ st → s.val p = o p) →
      (p ∉ st' → p ∈ st → False) → (p ∉ st' → val' p = s.val p) → val' g = s.val g →
      g ∉ st' →
      ∀ q c, c ∈ G.children q → k' q c = if c ∈ st' ∨ (c = g ∧ q ∈ ps) then o c else val' c := by
    intro val' st' hv hs hpush hpop hnp hvg hgst' q c hc
    by_cases e : q = p ∧ c = g
    · obtain ⟨rfl, rfl⟩ := e
      simp only [hk', and_self, ite_true]
      rw [ite_eq_right (by rintro (h1 | ⟨_, h2⟩); exacts [hgst' h1, hpn h2]), hvg]
    · simp only [hk', ite_eq_right e]
      rw [h.key q c hc]
      by_cases hcp : c = p
      · subst hcp
        have hcg : c ≠ g := hpg
        by_cases hin : c ∈ st
        · have hin' : c ∈ st' := by
            by_contra hn
            exact hpop hn hin
          rw [ite_eq_left (Or.inl hin), ite_eq_left (Or.inl hin')]
        · rw [ite_eq_right (by rintro (h1 | ⟨h2, _⟩); exacts [hin h1, hcg h2])]
          by_cases hin' : c ∈ st'
          · rw [ite_eq_left (Or.inl hin')]
            exact hpush hin' hin
          · rw [ite_eq_right (by rintro (h1 | ⟨h2, _⟩); exacts [hin' h1, hcg h2])]
            exact (hnp hin').symm
      · have e2 : (c ∈ st ∨ (c = g ∧ q ∈ p :: ps)) ↔ (c ∈ st' ∨ (c = g ∧ q ∈ ps)) := by
          rw [hs c hcp, List.mem_cons]
          constructor
          · rintro (h1 | ⟨h2, h3 | h3⟩)
            · exact Or.inl h1
            · exact absurd ⟨h3, h2⟩ e
            · exact Or.inr ⟨h2, h3⟩
          · rintro (h1 | ⟨h2, h3⟩)
            · exact Or.inl h1
            · exact Or.inr ⟨h2, Or.inr h3⟩
        by_cases hcnd : c ∈ st ∨ (c = g ∧ q ∈ p :: ps)
        · rw [ite_eq_left hcnd, ite_eq_left (e2.1 hcnd)]
        · rw [ite_eq_right hcnd, ite_eq_right (fun h' => hcnd (e2.2 h')), hv c hcp]
  have hrep' : ∀ q, Rep (Function.update s.hp p (updateKey (s.hp p) g (s.val g)).1 q)
      (G.children q).toFinset (k' q) (G.children q).length := by
    intro q
    by_cases e : q = p
    · rw [e, Function.update_self]
      exact hrepp
    · rw [Function.update_of_ne e]
      refine (h.rep q).congr (fun c _ => ?_)
      simp only [hk', e, false_and, ite_false]
  have hk'q : ∀ q, q ≠ p → k' q = k q := by
    intro q e
    funext c
    simp only [hk', e, false_and, ite_false]
  by_cases hc : findMax (updateKey (s.hp p) g (s.val g)).1 = s.val p
  · have E : dlvOne g (s.val g) p s st
        = (⟨s.val, Function.update s.hp p (updateKey (s.hp p) g (s.val g)).1⟩, st,
          (updateKey (s.hp p) g (s.val g)).2 + 1) := by
      unfold dlvOne
      rw [ite_eq_left hc]
    rw [E]
    refine ⟨k', ⟨hrep', fun q hq => ?_, hkey' s.val st (fun _ _ => rfl) (fun _ _ => Iff.rfl)
      (fun h1 h2 => absurd h1 h2) (fun h1 h2 => absurd h2 h1) (fun _ => rfl) rfl hgst,
      h.val, h.stk, h.nd, h.leaf⟩, hg, hgst, rfl, rfl, ?_, by dsimp only; omega, by dsimp only; omega⟩
    · show s.val q = _
      by_cases e : q = p
      · rw [e, ← hc, hM]
      · rw [hk'q q e]
        exact h.gate q hq
    · show (updateKey (s.hp p) g (s.val g)).2 + 1 + st.length
        ≤ Nat.clog 2 (G.children p).length + 3 + st.length
      omega
  · -- the value of `p` changes: by the delivery core it moves from old to final
    have hk1 : ∀ c ∈ G.children p, k p c = o c ∨ k p c = f c := fun c hc => hkof p c hc
    have hk2 : ∀ c ∈ G.children p, k' p c = o c ∨ k' p c = f c := by
      intro c hcm
      by_cases e : c = g
      · subst e
        right
        simp only [hk', and_self, ite_true]
        exact hg
      · have e' : k' p c = k p c := by simp only [hk', e, and_false, ite_false]
        rw [e']
        exact hkof p c hcm
    have hkk : ∀ c ∈ G.children p, k' p c = k p c ∨ (k p c = o c ∧ k' p c = f c) := by
      intro c _
      by_cases e : c = g
      · subst e
        right
        refine ⟨hkg, ?_⟩
        simp only [hk', and_self, ite_true]
        exact hg
      · left
        simp only [hk', e, and_false, ite_false]
    have hne : heapMax (G.children p) (k' p) ≠ heapMax (G.children p) (k p) := by
      rw [← hM, ← hV]
      exact hc
    obtain ⟨hVo, hMf⟩ := deliver_core hD (ho p hpint) (hf p hpint) hk1 hk2 hkk hne
    have hvp : s.val p = o p := hV.trans hVo
    have hMf' : findMax (updateKey (s.hp p) g (s.val g)).1 = f p := hM.trans hMf
    have hfo : f p ≠ o p := by
      intro e
      apply hc
      rw [hMf', hvp, e]
    have hpst : p ∉ st := fun hm => (h.stk p hm).2.1 (by
      have := (h.stk p hm).1
      rw [hvp] at this
      exact this.symm)
    have E : dlvOne g (s.val g) p s st
        = (⟨Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1),
            Function.update s.hp p (updateKey (s.hp p) g (s.val g)).1⟩, p :: st,
          (updateKey (s.hp p) g (s.val g)).2 + 2) := by
      unfold dlvOne
      rw [ite_eq_right hc]
    rw [E]
    have hgp' : g ≠ p := fun e => hpg e.symm
    have hv' : ∀ c, c ≠ p →
        Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1) c = s.val c :=
      fun c e => Function.update_of_ne e _ _
    have hvp' : Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1) p = f p := by
      rw [Function.update_self, hMf']
    have hU : Uset G o f ⟨Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1),
          Function.update s.hp p (updateKey (s.hp p) g (s.val g)).1⟩
        = (Uset G o f s).erase p := by
      ext q
      simp only [Uset, mem_filter, mem_erase, mem_range]
      by_cases e : q = p
      · subst e
        rw [hvp']
        simp [hfo]
      · rw [hv' q e]
        simp [e]
    have hpU : p ∈ Uset G o f s := by
      simp only [Uset, mem_filter, mem_range]
      exact ⟨hpN, hvp, hfo⟩
    have hcard := Finset.card_erase_add_one hpU
    have hR : Rset G o f ⟨Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1),
          Function.update s.hp p (updateKey (s.hp p) g (s.val g)).1⟩ (p :: st)
        = Rset G o f s st := by
      ext q
      simp only [Rset, mem_filter, mem_range, List.mem_cons]
      by_cases e : q = p
      · subst e
        simp [hfo, hvp, hpN]
      · rw [hv' q e]
        simp [e]
    refine ⟨k', ⟨hrep', fun q hq => ?_, hkey' _ (p :: st) hv' (fun c e => by simp [e])
      (fun _ _ => hvp) (fun h1 _ => h1 List.mem_cons_self)
      (fun h1 => absurd List.mem_cons_self h1) (hv' g hgp')
      (by simp [hgp', hgst]), fun q => ?_, fun q hq => ?_, List.nodup_cons.2 ⟨hpst, h.nd⟩,
      fun q hq => ?_⟩, by dsimp only; rw [hv' g hgp']; exact hg, by simp [hgp', hgst], ?_, hR, ?_,
      by dsimp only; omega, by simp⟩
    · show Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1) q = _
      by_cases e : q = p
      · rw [e, Function.update_self, hM]
      · rw [hv' q e, hk'q q e]
        exact h.gate q hq
    · show Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1) q = o q ∨
        Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1) q = f q
      by_cases e : q = p
      · rw [e, hvp']
        exact Or.inr rfl
      · rw [hv' q e]
        exact h.val q
    · show Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1) q = f q ∧
        f q ≠ o q ∧ q < G.N
      rcases List.mem_cons.1 hq with e | hm
      · rw [e, hvp']
        exact ⟨rfl, hfo, hpN⟩
      · have e : q ≠ p := fun e => hpst (e ▸ hm)
        rw [hv' q e]
        exact h.stk q hm
    · show Function.update s.val p (findMax (updateKey (s.hp p) g (s.val g)).1) q = f q
      have e : q ≠ p := fun e => hpint (e ▸ hq)
      rw [hv' q e]
      exact h.leaf q hq
    · rw [hU, List.length_cons]
      omega
    · show (updateKey (s.hp p) g (s.val g)).2 + 2 + st.length
        ≤ Nat.clog 2 (G.children p).length + 3 + (p :: st).length
      rw [List.length_cons]
      omega

/-- **All deliveries of a popped gate.** -/
theorem dlv_spec (hG : G.WF) (hD : Dir o f) (ho : Exact G o) (hf : Exact G f) (g : ℕ) (y : α) :
    ∀ (ps : List ℕ) (s : HEState α) (k : ℕ → ℕ → α) (st : List ℕ),
    DI G o f g ps s k st → s.val g = y → s.val g = f g → g ∉ st →
    (∀ p ∈ ps, g ∈ G.children p) → ps.Nodup →
    ∃ k', DI G o f g [] (dlv g y ps s st).1 k' (dlv g y ps s st).2.1 ∧
      (dlv g y ps s st).1.val g = f g ∧ g ∉ (dlv g y ps s st).2.1 ∧
      (dlv g y ps s st).2.1.length + (Uset G o f (dlv g y ps s st).1).card
        = st.length + (Uset G o f s).card ∧
      Rset G o f (dlv g y ps s st).1 (dlv g y ps s st).2.1 = Rset G o f s st ∧
      (dlv g y ps s st).2.2 + st.length
        ≤ (ps.map (fun p => Nat.clog 2 (G.children p).length + 3)).sum
          + (dlv g y ps s st).2.1.length ∧
      ps.length ≤ (dlv g y ps s st).2.2 ∧
      (dlv g y ps s st).2.1.length ≤ st.length + ps.length := by
  intro ps
  induction ps with
  | nil =>
    intro s k st h _ hg hgst _ _
    exact ⟨k, h, hg, hgst, rfl, rfl, by simp [dlv], by simp [dlv], by simp [dlv]⟩
  | cons p ps ih =>
    intro s k st h hy hg hgst hps hnd
    subst hy
    obtain ⟨k1, d1, d2, d3, d4, d5, d6, d7, d8⟩ := dlvOne_spec hG hD ho hf h hg hgst
      (hps p List.mem_cons_self) hnd
    have hy1 : (dlvOne g (s.val g) p s st).1.val g = s.val g := d2.trans hg.symm
    obtain ⟨k2, e1, e2, e3, e4, e5, e6, e7, e8⟩ := ih _ k1 _ d1 hy1 d2 d3
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) (List.nodup_cons.1 hnd).2
    refine ⟨k2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [dlv]; exact e1
    · rw [dlv]; exact e2
    · rw [dlv]; exact e3
    · rw [dlv]; dsimp only; omega
    · rw [dlv]; exact e5.trans d5
    · rw [dlv, List.map_cons, List.sum_cons]
      dsimp only
      omega
    · rw [dlv, List.length_cons]
      dsimp only
      omega
    · rw [dlv, List.length_cons]
      dsimp only
      omega

/-- **The stack loop.**  From a state satisfying the invariant (with no pending
deliveries), with enough fuel, the loop ends with every gate holding its final value and
every heap representing the final values of the children; its cost is at most
`|stack| + 1 + Σ_{q pending} wD q` and at least `Σ_{q pending} |parents q|`. -/
theorem loopD_spec (hG : G.WF) (hD : Dir o f) (ho : Exact G o) (hf : Exact G f) :
    ∀ (fuel : ℕ) (s : HEState α) (k : ℕ → ℕ → α) (st : List ℕ),
    DI G o f 0 [] s k st → st.length + (Uset G o f s).card < fuel →
    (∀ q, (loopD G fuel s st).1.val q = f q) ∧
    (∃ k' : ℕ → ℕ → α, (∀ p, Rep ((loopD G fuel s st).1.hp p) (G.children p).toFinset (k' p)
        (G.children p).length) ∧ ∀ p c, c ∈ G.children p → k' p c = f c) ∧
    (loopD G fuel s st).2 ≤ st.length + 1 + ∑ q ∈ Rset G o f s st, wD G q ∧
    ∑ q ∈ Rset G o f s st, (G.parents q).length ≤ (loopD G fuel s st).2 := by
  intro fuel
  induction fuel with
  | zero => intro s k st _ hm; omega
  | succ fuel ih =>
    intro s k st h hm
    cases st with
    | nil =>
      have hkey : ∀ p c, c ∈ G.children p → k p c = s.val c := by
        intro p c hc
        rw [h.key p c hc]
        simp
      have hex : Exact G s.val := fun p hp =>
        (h.gate p hp).trans (heapMax_congr (fun c hc => hkey p c hc))
      have hall : ∀ q, s.val q = f q := exact_unique hG hex hf (fun q hq => h.leaf q hq)
      have hR0 : ∑ q ∈ Rset G o f s [], (G.parents q).length = 0 := by
        apply sum_eq_zero
        intro q hq
        simp only [Rset, mem_filter, mem_range, List.not_mem_nil, or_false] at hq
        exact absurd (hall q ▸ hq.2.2) hq.2.1
      refine ⟨fun q => hall q, ⟨k, h.rep, fun p c hc => (hkey p c hc).trans (hall c)⟩, ?_, ?_⟩
      · show 1 ≤ _
        omega
      · rw [hR0]
        exact Nat.zero_le _
    | cons g rest =>
      obtain ⟨hg, hgo, hgN⟩ := h.stk g List.mem_cons_self
      obtain ⟨hgr, hrnd⟩ := List.nodup_cons.1 h.nd
      have hD' : DI G o f g (G.parents g) s k rest := by
        refine ⟨h.rep, h.gate, fun p c hc => ?_, h.val,
          fun q hq => h.stk q (List.mem_cons_of_mem _ hq), hrnd, h.leaf⟩
        rw [h.key p c hc]
        have hpc : p ∈ G.parents c := (hG.parents_iff c p).2 hc
        by_cases e : c = g
        · subst e
          simp [hpc]
        · simp [e]
      obtain ⟨k1, d1, _, _, d4, d5, d6, d7, d8⟩ := dlv_spec hG hD ho hf g (s.val g)
        (G.parents g) s k rest hD' rfl hg hgr (fun p hp => (hG.parents_iff g p).1 hp)
        (hG.parents_nodup g)
      have hm' : (dlv g (s.val g) (G.parents g) s rest).2.1.length
          + (Uset G o f (dlv g (s.val g) (G.parents g) s rest).1).card < fuel := by
        rw [d4]
        simp only [List.length_cons] at hm
        omega
      obtain ⟨i1, i2, i3, i4⟩ := ih _ k1 _ d1.reg hm'
      have hRins : Rset G o f s (g :: rest) = insert g (Rset G o f s rest) := by
        ext q
        simp only [Rset, mem_filter, mem_range, List.mem_cons, mem_insert]
        by_cases e : q = g
        · subst e
          simp [hgN, hgo]
        · simp [e]
      have hgR : g ∉ Rset G o f s rest := by
        simp only [Rset, mem_filter, mem_range, not_and, not_or]
        intro _ _
        exact ⟨fun e => hgo (hg ▸ e), hgr⟩
      rw [d5] at i3 i4
      have hw : wD G g = dcost G g + 2 * (G.parents g).length := rfl
      have hdc : dcost G g = ((G.parents g).map
          (fun p => Nat.clog 2 (G.children p).length + 3)).sum := rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [loopD]; exact i1
      · rw [loopD]; exact i2
      · rw [loopD, hRins, sum_insert hgR, List.length_cons]
        omega
      · rw [loopD, hRins, sum_insert hgR]
        omega

/-- **The wave without levels** (`eq:ram-work-bounds`, one endpoint, no term in `L`).  From
an implemented state representing a state that satisfies the engine invariant:

* `waveD` ends in an implemented state representing the result of the level-bucket wave
  `CostEngines.wave` (so `wave_spec` applies to it);
* its computed cost is at most `3 + Σ_{g changed} dcost g + 2 · (deliveries)`;
* its computed cost is at least the number of deliveries. -/
theorem waveD_spec (hG : G.WF) (x : ℕ) (y : α) (hs : HEState α) (s0 : EState α)
    (hx : x < G.N) (h : SimE G hs s0) (h0 : Inv G s0) :
    SimE G (waveD G x y hs).1 (wave G x y s0).1 ∧
    (waveD G x y hs).2 ≤ 3 + chgSum G s0 (wave G x y s0).1 + 2 * vol G s0 (wave G x y s0).1 ∧
    vol G s0 (wave G x y s0).1 ≤ (waveD G x y hs).2 := by
  obtain ⟨w1, w2, w3, _⟩ := wave_spec hG x y s0 hx h0
  have ho := inv_exact h0
  have hf := inv_exact w1
  have hD := dir_of_wave hG x y s0 hx h0
  have ht := HeapImpl.targetH_eq h x y x
  have hv := h.val
  by_cases hc : targetH G x y hs x = hs.val x
  · -- nothing changes
    have hxo : ∀ q, G.children q = [] → (wave G x y s0).1.val q = s0.val q := by
      intro q hq
      by_cases e : q = x
      · subst e
        rw [w2 hq]
        rw [ht, hv] at hc
        unfold target at hc
        rw [ite_eq_left hq, ite_eq_left rfl] at hc
        exact hc
      · exact w3 q hq e
    have hall : ∀ q, (wave G x y s0).1.val q = s0.val q := exact_unique hG hf ho hxo
    have hvol : vol G s0 (wave G x y s0).1 = 0 := by
      unfold vol
      apply sum_eq_zero
      intro q hq
      exact absurd (hall q) (mem_filter.1 hq).2
    unfold waveD
    rw [ite_eq_left hc]
    refine ⟨⟨by funext q; rw [hv, hall q], fun p => (h.hp p).congr (fun c hc' => ?_)⟩, ?_, ?_⟩
    · rw [h0.keys p c (List.mem_toFinset.1 hc'), w1.keys p c (List.mem_toFinset.1 hc'), hall c]
    · show 1 ≤ _
      omega
    · rw [hvol]
      exact Nat.zero_le _
  · -- `x` is a leaf whose value changes
    have hxl : G.children x = [] := by
      by_contra hxl
      apply hc
      rw [ht, hv]
      unfold target
      rw [ite_eq_right hxl]
      exact (h0.gate x hxl).symm
    have hty : targetH G x y hs x = y := by
      rw [ht]
      unfold target
      rw [ite_eq_left hxl, ite_eq_left rfl]
    have hfx : (wave G x y s0).1.val x = y := w2 hxl
    have hfo : (wave G x y s0).1.val x ≠ s0.val x := by
      rw [hfx, ← hty, ← hv]
      exact hc
    set s1 : HEState α := ⟨Function.update hs.val x (targetH G x y hs x), hs.hp⟩ with hs1
    have hs1x : s1.val x = (wave G x y s0).1.val x := by
      rw [hs1]
      show Function.update hs.val x (targetH G x y hs x) x = _
      rw [Function.update_self, hty, hfx]
    have hs1o : ∀ q, q ≠ x → s1.val q = s0.val q := by
      intro q e
      rw [hs1]
      show Function.update hs.val x (targetH G x y hs x) q = _
      rw [Function.update_of_ne e, hv]
    have hDI : DI G s0.val (wave G x y s0).1.val 0 [] s1 s0.key [x] := by
      refine ⟨h.hp, fun p hp => ?_, fun p c hcp => ?_, fun q => ?_, fun q hq => ?_,
        List.nodup_singleton x, fun q hq => ?_⟩
      · have e : p ≠ x := fun e => hp (e ▸ hxl)
        rw [hs1o p e]
        exact h0.gate p hp
      · rw [h0.keys p c hcp]
        by_cases e : c = x
        · subst e
          simp
        · simp only [List.mem_singleton, e, false_or, List.not_mem_nil, and_false, ite_false]
          exact (hs1o c e).symm
      · by_cases e : q = x
        · subst e; exact Or.inr hs1x
        · exact Or.inl (hs1o q e)
      · rw [List.mem_singleton] at hq
        subst hq
        exact ⟨hs1x, hfo, hx⟩
      · by_cases e : q = x
        · subst e; exact hs1x
        · rw [hs1o q e]; exact (w3 q hq e).symm
    have hUle : (Uset G s0.val (wave G x y s0).1.val s1).card ≤ G.N := by
      have := card_filter_le (range G.N)
        (fun q => s1.val q = s0.val q ∧ (wave G x y s0).1.val q ≠ s0.val q)
      rw [card_range] at this
      exact this
    obtain ⟨l1, ⟨k', l2a, l2b⟩, l3, l4⟩ := loopD_spec hG hD ho hf (G.N + 2) s1 s0.key [x] hDI
      (by simp only [List.length_singleton]; omega)
    have hR : Rset G s0.val (wave G x y s0).1.val s1 [x]
        = (range G.N).filter (fun q => (wave G x y s0).1.val q ≠ s0.val q) := by
      apply filter_congr
      intro q _
      by_cases e : q = x
      · subst e
        simp
      · simp [e, hs1o q e]
    rw [hR] at l3 l4
    have hsum : ∑ q ∈ (range G.N).filter (fun q => (wave G x y s0).1.val q ≠ s0.val q), wD G q
        = chgSum G s0 (wave G x y s0).1 + 2 * vol G s0 (wave G x y s0).1 := by
      unfold wD chgSum vol
      rw [sum_add_distrib, mul_sum]
    rw [hsum] at l3
    unfold waveD
    rw [ite_eq_right hc, ← hs1]
    refine ⟨⟨funext l1, fun p => (l2a p).congr (fun c hc' => ?_)⟩, ?_, ?_⟩
    · rw [l2b p c (List.mem_toFinset.1 hc'), w1.keys p c (List.mem_toFinset.1 hc')]
    · show 1 + _ ≤ _
      simp only [List.length_singleton] at l3
      omega
    · show _ ≤ 1 + _
      unfold vol
      omega

end DFS

/-! ## 3. The engines with `waveD`, and the assembled display -/

section EngineED

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- **Graph-Eager with `waveD`**: both endpoints after `t` rollouts. -/
def runED (G : Dag) (u : ℕ → ℕ × α × α) (s0 : HEState α × HEState α) :
    ℕ → HEState α × HEState α
  | 0 => s0
  | t + 1 => ((waveD G (u (t + 1)).1 (u (t + 1)).2.1 (runED G u s0 t).1).1,
      (waveD G (u (t + 1)).1 (u (t + 1)).2.2 (runED G u s0 t).2).1)

/-- Computed cost of the full query of time `t` (if any, `2K`) and of the two waves of
rollout `t + 1`. -/
def costED (G : Dag) (K : ℕ) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : HEState α × HEState α) (t : ℕ) : ℕ :=
  (if q t = true then 2 * K else 0)
    + (waveD G (u (t + 1)).1 (u (t + 1)).2.1 (runED G u s0 t).1).2
    + (waveD G (u (t + 1)).1 (u (t + 1)).2.2 (runED G u s0 t).2).2

variable {G0 : Dag} {u : ℕ → ℕ × α × α} {lo0 hi0 : EState α}

/-- **Graph-Eager with `waveD`.**  The implemented engine represents `CostEngines.runState`
at every time, and step `t` costs between `eagerPlus t` and
`2K·[query] + 6 + (⌈log₂ D⌉ + 5) · eagerPlus t`. -/
theorem runED_spec (hG : G0.WF) (D : ℕ) (hD : ∀ p, (G0.children p).length ≤ D)
    (h0 : RInv G0 ⟨G0, lo0, hi0⟩) (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (K : ℕ)
    (q : ℕ → Bool) (hl hu : HEState α) (sl : SimE G0 hl lo0) (su : SimE G0 hu hi0) (t : ℕ) :
    SimE G0 (runED G0 u (hl, hu) t).1 (runState G0 u (lo0, hi0) t).1 ∧
    SimE G0 (runED G0 u (hl, hu) t).2 (runState G0 u (lo0, hi0) t).2 ∧
    eagerPlus G0 u lo0 hi0 t ≤ costED G0 K u q (hl, hu) t ∧
    costED G0 K u q (hl, hu) t
      ≤ (if q t = true then 2 * K else 0) + 6 + (Nat.clog 2 D + 5) * eagerPlus G0 u lo0 hi0 t := by
  have hsim : ∀ t, SimE G0 (runED G0 u (hl, hu) t).1 (runState G0 u (lo0, hi0) t).1 ∧
      SimE G0 (runED G0 u (hl, hu) t).2 (runState G0 u (lo0, hi0) t).2 := by
    intro t
    induction t with
    | zero => exact ⟨sl, su⟩
    | succ t ih =>
      obtain ⟨i1, i2, _, _⟩ := live_eq_eager (cand := noCand) hG h0 hn t
      obtain ⟨a, _, _, _⟩ := hn t
      exact ⟨(waveD_spec hG (u (t + 1)).1 (u (t + 1)).2.1 _ _ a ih.1 i1).1,
        (waveD_spec hG (u (t + 1)).1 (u (t + 1)).2.2 _ _ a ih.2 i2).1⟩
  refine ⟨(hsim t).1, (hsim t).2, ?_⟩
  obtain ⟨i1, i2, _, _⟩ := live_eq_eager (cand := noCand) hG h0 hn t
  obtain ⟨a, _, _, _⟩ := hn t
  obtain ⟨_, l2, l3⟩ := waveD_spec hG (u (t + 1)).1 (u (t + 1)).2.1 _ _ a (hsim t).1 i1
  obtain ⟨_, u2, u3⟩ := waveD_spec hG (u (t + 1)).1 (u (t + 1)).2.2 _ _ a (hsim t).2 i2
  have bl := (chgSum_bounds D hD (runState G0 u (lo0, hi0) t).1
    (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1).2
  have bh := (chgSum_bounds D hD (runState G0 u (lo0, hi0) t).2
    (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1).2
  have hp : eagerPlus G0 u lo0 hi0 t
      = vol G0 (runState G0 u (lo0, hi0) t).1
          (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
        + vol G0 (runState G0 u (lo0, hi0) t).2
          (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1 := rfl
  have hexp : (Nat.clog 2 D + 5)
        * (vol G0 (runState G0 u (lo0, hi0) t).1
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
          + vol G0 (runState G0 u (lo0, hi0) t).2
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1)
      = (Nat.clog 2 D + 3) * vol G0 (runState G0 u (lo0, hi0) t).1
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
        + 2 * vol G0 (runState G0 u (lo0, hi0) t).1
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.1 (runState G0 u (lo0, hi0) t).1).1
        + ((Nat.clog 2 D + 3) * vol G0 (runState G0 u (lo0, hi0) t).2
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1
          + 2 * vol G0 (runState G0 u (lo0, hi0) t).2
            (wave G0 (u (t + 1)).1 (u (t + 1)).2.2 (runState G0 u (lo0, hi0) t).2).1) := by
    ring
  rw [hp, hexp]
  unfold costED
  constructor
  · omega
  · omega

end EngineED

section EngineSD

variable {α : Type*} [LinearOrder α] [OrderBot α]

/-- The backup waves of one terminal update on the live circuit, with `waveD`. -/
def waveStepD (u : ℕ × α × α) (s : HRState α) : HRState α × ℕ :=
  (⟨s.G, (waveD s.G u.1 u.2.1 s.lo).1, (waveD s.G u.1 u.2.2 s.hi).1⟩,
   (waveD s.G u.1 u.2.1 s.lo).2 + (waveD s.G u.1 u.2.2 s.hi).2)

/-- **One rollout of Graph-Selective with `waveD`**: the waves, then the retirement pass and
the release cascade of `LiteralE4.tailStep`. -/
def relStepD (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ × α × α) (s : HQS α) :
    HQS α × ℕ :=
  ((LiteralE4.tailStep K rt candV s (waveStepD u s.r).1).1,
   (waveStepD u s.r).2 + (LiteralE4.tailStep K rt candV s (waveStepD u s.r).1).2)

variable {K : ℕ} {rt : ℕ → ℕ}

/-- The part after the waves, from ANY implemented state representing the post-wave state. -/
theorem tailStep_gen (candV : Policy α) {hs : HQS α} {s : QS α} (h : SimQ hs s)
    (u : ℕ × α × α) {w : HRState α} (hw : SimR w (waveStep u s.r).1) :
    SimQ (LiteralE4.tailStep K rt candV hs w).1 (relStep K rt (liftCand candV) u s).1 ∧
    (LiteralE4.tailStep K rt candV hs w).2
      ≤ 2 * ((retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).2
        + (releaseLoop (protOf K rt s.act)
            (relFuel (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G
              ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd))
            ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd)
            (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G).2) := by
  obtain ⟨hr, hact⟩ := h
  have hc : candV hs.r.G hs.r.lo.val hs.r.hi.val w.lo.val w.hi.val
      = liftCand candV s.r (waveStep u s.r).1 := by
    unfold liftCand
    rw [hr.G, hr.lo.val, hr.hi.val, hw.lo.val, hw.hi.val]
  obtain ⟨r1, r2⟩ := retireListH_sim (liftCand candV s.r (waveStep u s.r).1) hw
  have hG1 : (retireListH (liftCand candV s.r (waveStep u s.r).1) w).1.G
      = (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G := r1.G
  obtain ⟨l1, l2⟩ := releaseLoopH_sim (protOf K rt s.act)
    (relFuel (retireList (liftCand candV s.r (waveStep u s.r).1) (waveStep u s.r).1).1.G
      ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd))
    ((liftCand candV s.r (waveStep u s.r).1).map Prod.snd) _ _ r1
  unfold LiteralE4.tailStep
  rw [hc, hG1, hact]
  refine ⟨⟨l1, rfl⟩, ?_⟩
  show (retireListH _ w).2 + (releaseLoopH _ _ _ _).2 ≤ _
  rw [l2]
  omega

/-- **One rollout with `waveD`.**  From an implemented state representing a state that
satisfies the coupled invariant, the rollout represents the abstract rollout
`RetireFinal.relStep`; its computed cost plus the four level scans `4 (L + 3)` of the two
abstract waves is at most `6 + 2 · (live deliveries) + 2 · (charged cost of relStep)`;
and it is at least the number of live deliveries. -/
theorem relStepD_spec (candV : Policy α) {hs : HQS α} {s : QS α} (h : SimQ hs s) {G0 : Dag}
    {elo ehi : ℕ → α} (hinv : CInv G0 K rt s.r s.act elo ehi) (u : ℕ × α × α)
    (hx : u.1 < G0.N) :
    SimQ (relStepD K rt candV u hs).1 (relStep K rt (liftCand candV) u s).1 ∧
    (relStepD K rt candV u hs).2 + 4 * (G0.L + 3)
      ≤ 6 + 2 * (vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1
            + vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1)
        + 2 * (relStep K rt (liftCand candV) u s).2 ∧
    vol s.r.G s.r.lo (wave s.r.G u.1 u.2.1 s.r.lo).1
        + vol s.r.G s.r.hi (wave s.r.G u.1 u.2.2 s.r.hi).1
      ≤ (relStepD K rt candV u hs).2 := by
  have hGeq : hs.r.G = s.r.G := h.r.G
  have hxs : u.1 < s.r.G.N := by rw [hinv.nEq]; exact hx
  obtain ⟨l1, l2, l3⟩ := waveD_spec hinv.wf u.1 u.2.1 hs.r.lo s.r.lo hxs h.r.lo hinv.invLo
  obtain ⟨u1, u2, u3⟩ := waveD_spec hinv.wf u.1 u.2.2 hs.r.hi s.r.hi hxs h.r.hi hinv.invHi
  obtain ⟨_, _, _, lw⟩ := wave_spec hinv.wf u.1 u.2.1 s.r.lo hxs hinv.invLo
  obtain ⟨_, _, _, uw⟩ := wave_spec hinv.wf u.1 u.2.2 s.r.hi hxs hinv.invHi
  rw [hinv.lEq] at lw uw
  have hw : SimR (waveStepD u hs.r).1 (waveStep u s.r).1 := by
    refine ⟨hGeq, ?_, ?_⟩
    · show SimE s.r.G (waveD hs.r.G u.1 u.2.1 hs.r.lo).1 (wave s.r.G u.1 u.2.1 s.r.lo).1
      rw [hGeq]; exact l1
    · show SimE s.r.G (waveD hs.r.G u.1 u.2.2 hs.r.hi).1 (wave s.r.G u.1 u.2.2 s.r.hi).1
      rw [hGeq]; exact u1
  obtain ⟨t1, t2⟩ := tailStep_gen (K := K) (rt := rt) candV h u hw
  have eS : (relStepD K rt candV u hs).2
      = (waveD s.r.G u.1 u.2.1 hs.r.lo).2 + (waveD s.r.G u.1 u.2.2 hs.r.hi).2
        + (LiteralE4.tailStep K rt candV hs (waveStepD u hs.r).1).2 := by
    show (waveD hs.r.G u.1 u.2.1 hs.r.lo).2 + (waveD hs.r.G u.1 u.2.2 hs.r.hi).2
        + (LiteralE4.tailStep K rt candV hs (waveStepD u hs.r).1).2 = _
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
  refine ⟨t1, ?_, ?_⟩
  · rw [eS, eA, lw, uw]
    omega
  · rw [eS]
    omega

/-- State of Graph-Selective with `waveD` after `t` rollouts (queries with root retirement
as in `RetireFinal.runH`). -/
def runSD (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : HQS α) : ℕ → HQS α
  | 0 => s0
  | t + 1 => (relStepD K rt candV (u (t + 1))
      (if q t = true then (qRetireH K rt (runSD K rt candV u q s0 t)).1
        else runSD K rt candV u q s0 t)).1

/-- Computed cost of the query of time `t` (if any) and of rollout `t + 1`. -/
def costSD (K : ℕ) (rt : ℕ → ℕ) (candV : Policy α) (u : ℕ → ℕ × α × α) (q : ℕ → Bool)
    (s0 : HQS α) (t : ℕ) : ℕ :=
  (if q t = true then K + (qRetireH K rt (runSD K rt candV u q s0 t)).2 else 0)
    + (relStepD K rt candV (u (t + 1))
        (if q t = true then (qRetireH K rt (runSD K rt candV u q s0 t)).1
          else runSD K rt candV u q s0 t)).2

variable {G0 : Dag} {u : ℕ → ℕ × α × α} {lo0 hi0 : EState α}

/-- **The run with `waveD`.**  At every time the engine represents `RetireFinal.runF`; the
cost of step `t` is at most `6 + 2 · volF t + 2 · costF t - 4 (L + 3)` and at least
`volF t`. -/
theorem runSD_spec (hG : G0.WF) (h0 : RInv G0 ⟨G0, lo0, hi0⟩)
    (hn : NestedRun G0 noCand u ⟨G0, lo0, hi0⟩) (q : ℕ → Bool) (hr0 : HRState α)
    (hsim : SimR hr0 ⟨G0, lo0, hi0⟩) (act0 : ℕ → Bool) (t : ℕ) :
    SimQ (runSD K rt delivV u q ⟨hr0, act0⟩ t) (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t) ∧
    costSD K rt delivV u q ⟨hr0, act0⟩ t + 4 * (G0.L + 3)
      ≤ 6 + 2 * volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t
        + 2 * costF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t ∧
    volF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t ≤ costSD K rt delivV u q ⟨hr0, act0⟩ t := by
  have hpinv := fun t => preF_inv (K := K) (rt := rt) (cand := delivCand) (q := q)
    (act0 := act0) hG h0 hn t
  have hpre : ∀ t, SimQ (runSD K rt delivV u q ⟨hr0, act0⟩ t)
      (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t) →
      SimQ (if q t = true then (qRetireH K rt (runSD K rt delivV u q ⟨hr0, act0⟩ t)).1
        else runSD K rt delivV u q ⟨hr0, act0⟩ t)
      (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t) := by
    intro t ih
    unfold preF
    by_cases hq : q t = true
    · rw [ite_eq_left hq, ite_eq_left hq]
      exact (qRetireH_sim K rt ih).1
    · rw [ite_eq_right hq, ite_eq_right hq]
      exact ih
  have hS : ∀ t, SimQ (runSD K rt delivV u q ⟨hr0, act0⟩ t)
      (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t) := by
    intro t
    induction t with
    | zero => exact ⟨hsim, rfl⟩
    | succ t ih =>
      exact (relStepD_spec delivV (hpre t ih) (hpinv t) (u (t + 1)) (hn t).1).1
  refine ⟨hS t, ?_⟩
  obtain ⟨_, c2, c3⟩ := relStepD_spec delivV (hpre t (hS t)) (hpinv t) (u (t + 1)) (hn t).1
  obtain ⟨e1, e2, _⟩ := rstep_endpoints delivCand (u (t + 1))
    (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r
  have elo : (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.lo
      = (wave (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G (u (t + 1)).1
          (u (t + 1)).2.1 (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.lo).1 := e1
  have ehi : (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ (t + 1)).r.hi
      = (wave (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.G (u (t + 1)).1
          (u (t + 1)).2.2 (preF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t).r.hi).1 := e2
  have hq2 : (if q t = true then K + (qRetireH K rt (runSD K rt delivV u q ⟨hr0, act0⟩ t)).2
        else 0)
      = (if q t = true then K + (qRetire K rt
          (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2 else 0) := by
    rw [(qRetireH_sim K rt (hS t)).2]
  have hcS : costSD K rt delivV u q ⟨hr0, act0⟩ t
      = (if q t = true then K + (qRetire K rt
          (runF K rt delivCand u q ⟨⟨G0, lo0, hi0⟩, act0⟩ t)).2 else 0)
        + (relStepD K rt delivV (u (t + 1))
            (if q t = true then (qRetireH K rt (runSD K rt delivV u q ⟨hr0, act0⟩ t)).1
              else runSD K rt delivV u q ⟨hr0, act0⟩ t)).2 := by
    unfold costSD
    rw [hq2]
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
  · have key : ∀ (X cs kv A : ℕ), cs + 4 * (G0.L + 3) ≤ 6 + 2 * kv + 2 * A →
        X + cs + 4 * (G0.L + 3) ≤ 6 + 2 * kv + 2 * (X + A) := by
      intros
      omega
    exact key _ _ _ _ c2
  · exact c3.trans (Nat.le_add_left _ _)

end EngineSD

/-! ### The assembled display -/

section Final

variable {α : Type*} [LinearOrder α] [OrderBot α] (R : LiteralE4.Traj α)

/-- The initialised lower-endpoint state on heaps built bottom-up. -/
def hloB : HEState α := (initPassB R.G0 R.order R.hl).1

/-- The initialised upper-endpoint state on heaps built bottom-up. -/
def hhiB : HEState α := (initPassB R.G0 R.order R.hu).1

/-- Computed cost of the initialisation with bottom-up heaps (both endpoints). -/
def initWB : ℕ := (initPassB R.G0 R.order R.hl).2 + (initPassB R.G0 R.order R.hu).2

/-- **`W_eager`** with bottom-up initialisation and `waveD`. -/
def WeagerD : ℕ :=
  initWB R + R.samp + ∑ t ∈ range R.T, costED R.G0 R.K R.u R.q (hloB R, hhiB R) t

/-- **`W_live`** with bottom-up initialisation and `waveD`. -/
def WliveD : ℕ :=
  initWB R + R.samp
    + ∑ t ∈ range R.T, costSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t

/-- Leader-and-stop output of the implemented Graph-Eager engine (all actions scanned). -/
noncomputable def outED (t : ℕ) : Option ℕ × Bool :=
  qOut R.φ R.ε R.K (fun i => (runED R.G0 R.u (hloB R, hhiB R) t).1.val (R.rt i))
    (fun i => (runED R.G0 R.u (hloB R, hhiB R) t).2.val (R.rt i)) (fun _ => true)

/-- Leader-and-stop output of the implemented Graph-Selective engine (active actions). -/
noncomputable def outSD (t : ℕ) : Option ℕ × Bool :=
  qOut R.φ R.ε R.K
    (fun i => (runSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t).r.lo.val
      (R.rt i))
    (fun i => (runSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t).r.hi.val
      (R.rt i))
    (runSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t).act

lemma sum_map_lin (d : ℕ → ℕ) : ∀ l : List ℕ,
    (l.map (fun g => 4 * d g + 2)).sum = 4 * (l.map d).sum + 2 * l.length
  | [] => rfl
  | g :: l => by
      simp only [List.map_cons, List.sum_cons, List.length_cons, sum_map_lin d l]
      ring

/-- **Linear initialisation** (`eq:ram-work-bounds`, the term `|V| + |E|`). -/
theorem initB_spec :
    SimE R.G0 (hloB R) R.lo0 ∧ SimE R.G0 (hhiB R) R.hi0 ∧ RInv R.G0 ⟨R.G0, R.lo0, R.hi0⟩ ∧
    initWB R ≤ 4 * (R.G0.N + 2 * live R.G0) := by
  obtain ⟨i1, _⟩ := init_engine R.wf R.order (⟨R.hl.val, fun _ _ => ⊥⟩ : EState α)
    ⟨R.hu.val, fun _ _ => ⊥⟩ R.order_all R.order_int R.order_sorted R.leaf
  obtain ⟨l1, l2⟩ := initPassB_sim (G := R.G0) R.order R.hl ⟨R.hl.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_lo
  obtain ⟨u1, u2⟩ := initPassB_sim (G := R.G0) R.order R.hu ⟨R.hu.val, fun _ _ => ⊥⟩ R.nodup
    R.order_all rfl R.empty_hi
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
  rw [sum_map_lin] at l2 u2
  refine ⟨l1, u1, i1, ?_⟩
  unfold initWB
  omega

/-- **`prop:uct-coupling` with `eq:ram-work-bounds`, linear initialisation and
`O(log (2 + D))` per delivery.**  For a coupled trajectory `R` (`LiteralE4.Traj`: `T`
rollouts, `Q` root queries, `K ≥ 1` root actions, out-degree at most `D`, `S₀`
full-incidence deliveries, `S` live deliveries, `R` permanent retirements), with
initialisation by `initPassB` (bottom-up heaps), Graph-Eager `runED` and Graph-Selective
`runSD` (both with the level-free scheduler `waveD`), and all heap operations executed by
the implemented programs:

1. both engines return the same leader and the same stopping bit at every time;
2. `T + S₀ ≤ W_eager ≤ initW + samp + 6T + 2QK + (⌈log₂ D⌉ + 5) S₀`;
3. `T + S ≤ W_live ≤ initW + samp + 6T + 8QK + 2 (⌈log₂ D⌉ + 6) S
      + 2 (2⌈log₂ D⌉ + 4) R + 4 (|V| + |E|)`;
4. `initW ≤ 4 (|V| + 2 |E|)`, `T ≤ samp ≤ T (L + 1)(D + 1)`, `S ≤ S₀`, `R ≤ |E|`.

There is no term in `L` other than inside `samp`. -/
theorem ram_work_bounds_display :
    (∀ t, outSD R t = outED R t) ∧
    (R.T + R.S0 ≤ WeagerD R) ∧
    (WeagerD R ≤ initWB R + R.samp + 6 * R.T + 2 * (R.Q * R.K)
      + (Nat.clog 2 R.D + 5) * R.S0) ∧
    (R.T + R.S ≤ WliveD R) ∧
    (WliveD R ≤ initWB R + R.samp + 6 * R.T + 8 * (R.Q * R.K)
      + 2 * ((Nat.clog 2 R.D + 6) * R.S)
      + 2 * ((2 * Nat.clog 2 R.D + 4) * R.Rret) + 4 * (R.G0.N + live R.G0)) ∧
    (initWB R ≤ 4 * (R.G0.N + 2 * live R.G0)) ∧
    (R.T ≤ R.samp ∧ R.samp ≤ R.T * ((R.G0.L + 1) * (R.D + 1))) ∧
    (R.S ≤ R.S0) ∧ (R.Rret ≤ live R.G0) := by
  obtain ⟨sl, su, h0, hinit⟩ := initB_spec R
  have hn : NestedRun R.G0 noCand R.u ⟨R.G0, R.lo0, R.hi0⟩ := R.nested
  have hsimR : SimR (⟨R.G0, hloB R, hhiB R⟩ : HRState α) ⟨R.G0, R.lo0, R.hi0⟩ := ⟨rfl, sl, su⟩
  obtain ⟨sa, sb⟩ := R.samp_bounds
  have hE := fun t => runED_spec R.wf R.D R.deg h0 hn R.K R.q (hloB R) (hhiB R) sl su t
  have hSp := fun t => runSD_spec (K := R.K) (rt := R.rt) R.wf h0 hn R.q
    (⟨R.G0, hloB R, hhiB R⟩ : HRState α) hsimR (fun _ => true) t
  obtain ⟨b1, _, _, _, f5, f6, f7⟩ := ram_work_bounds_final R.wf R.D R.deg h0 hn R.hK R.rt
    R.φ R.hφ R.ε R.hε R.q R.T 0
  have hEl : ∑ t ∈ range R.T, eagerPlus R.G0 R.u R.lo0 R.hi0 t
      ≤ ∑ t ∈ range R.T, costED R.G0 R.K R.u R.q (hloB R, hhiB R) t :=
    sum_le_sum (fun t _ => (hE t).2.2.1)
  have hEu : ∑ t ∈ range R.T, costED R.G0 R.K R.u R.q (hloB R, hhiB R) t
      ≤ 2 * (R.Q * R.K) + 6 * R.T
        + (Nat.clog 2 R.D + 5) * ∑ t ∈ range R.T, eagerPlus R.G0 R.u R.lo0 R.hi0 t := by
    calc ∑ t ∈ range R.T, costED R.G0 R.K R.u R.q (hloB R, hhiB R) t
        ≤ ∑ t ∈ range R.T, ((if R.q t = true then 2 * R.K else 0) + 6
          + (Nat.clog 2 R.D + 5) * eagerPlus R.G0 R.u R.lo0 R.hi0 t) :=
          sum_le_sum (fun t _ => (hE t).2.2.2)
      _ = 2 * (R.Q * R.K) + 6 * R.T
          + (Nat.clog 2 R.D + 5) * ∑ t ∈ range R.T, eagerPlus R.G0 R.u R.lo0 R.hi0 t := by
          rw [sum_add_distrib, sum_add_distrib, ← sum_filter, sum_const, sum_const, card_range,
            ← mul_sum, smul_eq_mul, smul_eq_mul]
          unfold LiteralE4.Traj.Q
          ring
  have hSl : ∑ t ∈ range R.T,
        volF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t
      ≤ ∑ t ∈ range R.T,
        costSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t :=
    sum_le_sum (fun t _ => (hSp t).2.2)
  have hSu : ∑ t ∈ range R.T,
        costSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t
        + R.T * (4 * (R.G0.L + 3))
      ≤ 6 * R.T
        + 2 * ∑ t ∈ range R.T,
          volF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t
        + 2 * ∑ t ∈ range R.T,
          costF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t := by
    calc ∑ t ∈ range R.T,
          costSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t
          + R.T * (4 * (R.G0.L + 3))
        = ∑ t ∈ range R.T,
          (costSD R.K R.rt delivV R.u R.q ⟨⟨R.G0, hloB R, hhiB R⟩, fun _ => true⟩ t
            + 4 * (R.G0.L + 3)) := by
          rw [sum_add_distrib, sum_const, card_range, smul_eq_mul]
      _ ≤ ∑ t ∈ range R.T, (6
          + 2 * volF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t
          + 2 * costF R.K R.rt delivCand R.u R.q ⟨⟨R.G0, R.lo0, R.hi0⟩, fun _ => true⟩ t) :=
          sum_le_sum (fun t _ => (hSp t).2.1)
      _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, sum_const, card_range, ← mul_sum,
            ← mul_sum, smul_eq_mul]
          ring
  have hTL : R.T * (4 * (R.G0.L + 3)) = 2 * (2 * R.T * (R.G0.L + 3)) := by ring
  have hQK : ((range R.T).filter (fun t => R.q t = true)).card * (4 * R.K)
      = 4 * (R.Q * R.K) := by
    unfold LiteralE4.Traj.Q
    ring
  have hx1 : (Nat.clog 2 R.D + 6) * R.S = (Nat.clog 2 R.D + 5) * R.S + R.S := by ring
  refine ⟨fun t => ?_, ?_, ?_, ?_, ?_, hinit, ⟨sa, sb⟩, f6, f7⟩
  · obtain ⟨sr, sa'⟩ := (hSp t).1
    unfold outSD outED
    rw [sr.lo.val, sr.hi.val, sa', b1 t, (hE t).1.val, (hE t).2.1.val]
  · unfold WeagerD LiteralE4.Traj.S0
    omega
  · unfold WeagerD LiteralE4.Traj.S0
    omega
  · unfold WliveD LiteralE4.Traj.S
    omega
  · rw [hx1]
    unfold WliveD LiteralE4.Traj.S LiteralE4.Traj.Rret
    rw [hQK] at f5
    rw [hTL] at hSu
    omega

end Final

end LiteralE7a
end JointRootCert
