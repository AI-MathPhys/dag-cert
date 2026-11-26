/-
Unknown-variance Gaussian tracking: `(ε, δ)`-correctness of the sparse four-power tracker on
intrinsic tapes (manuscript, Theorem `thm:v34-adaptive` "Sparse four-power nuisance-KL tracking
with unknown variances"; Theorem `thm:v34-action-local` "Action-local optional evaluation and
intersection-union root coverage" for the tracker's batch model; construction and proofs in
`app:v34-theory`).

The tracker is `Tracker` of `UnknownVarianceTracker.lean`: a deterministic function of the
intrinsic tapes `Y x n`, whose batch `i + 1` is, for each query type, the tape segment starting
at the number of observations of that type consumed so far, of predictable length.

Results.

1. Adaptive-segment freshness.  `lintegral_adaptive_segment`: for jointly independent
   observations and a count vector that only reads the observations it counts,
   `E[G(consumed block, next segment)] = E[∫ G(consumed block, s) dπ(s)]`, `π` the law of the
   segment at the frozen counts; `map_tapeShift_eq`: for identically distributed observations
   `π` is the law of the whole tape.  `lintegral_adaptive_segment_le` is the one-step
   inequality.  The proof decomposes over the countably many count vectors
   (`indepFun_trunc_shift`, `lintegral_block_freeze`); no strong Markov theorem is used.
2. Supermartingale and coverage.  `Tracker.state_meas` (a run is a measurable function of the
   tape), `Tracker.state_congr` (a run only reads consumed observations),
   `Tracker.obsFiltration` (the filtration of consumed observations),
   `Tracker.factorWealth_supermartingale`, `Tracker.idealWealth_supermartingale` (the
   likelihood-ratio wealth `∏ ½ (1 + q_i / p_i)` is a supermartingale),
   `Tracker.wealth_le_idealWealth` (it dominates the tracker's wealth under a component null),
   `Tracker.wealth_supermartingale` (the tracker's own wealth is a supermartingale when the
   certified bounds are adapted), and `Tracker.coverage`: the probability that the test ever
   passes with an incorrect selected action is at most `δ`.
3. Non-vacuity.  `Tracker.canonical` with `Tracker.canonical_contract`,
   `Tracker.canonical_meas`, `Tracker.canonical_boundsAdapted`.
4. `v34_adaptive`: `(ε, δ)`-correctness together with the sharp rate of `v34_adaptive_rate`.

Hypotheses beyond `Tracker.Contract`.  `Tracker.Meas`: the design oracle, its displayed score,
the tie-breaking rule and the rounding rule are Borel functions of their real arguments.  The
manuscript does not state this; it is needed for the stopping event to be measurable.  Nothing
is assumed about measurability of the certified bounds `qlo`, `Uhi` in the coverage theorem.
Independence is joint over `(x, n)` (the manuscript's "independent across query types"),
whereas the rate half only uses independence within each type.
-/
import JointRootCert.UnknownVarianceTracker

namespace JointRootCert

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ### Tapes: truncation, shift, and adaptive-segment freshness -/

section Tape

variable {X : Type*}

/-- The tape realization of a family of observations. -/
def tapeOf {Ω : Type*} (Y : X → ℕ → Ω → ℝ) (ω : Ω) : X → ℕ → ℝ := fun x n => Y x n ω

/-- The tape with every entry at position `≥ c x` of type `x` erased: the observations
consumed when the counts are `c`. -/
def tapeTrunc (c : X → ℕ) (y : X → ℕ → ℝ) : X → ℕ → ℝ := fun x n => if n < c x then y x n else 0

/-- The tape read from position `c x` on for every type `x`: the segment starting at the
counts `c`. -/
def tapeShift (c : X → ℕ) (y : X → ℕ → ℝ) : X → ℕ → ℝ := fun x ℓ => y x (c x + ℓ)

lemma measurable_tapeTrunc (c : X → ℕ) : Measurable (tapeTrunc c) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun n => ?_
  unfold tapeTrunc
  by_cases h : n < c x
  · simp only [h, ↓reduceIte]
    exact (measurable_pi_apply n).comp (measurable_pi_apply x)
  · simp only [h, ↓reduceIte]
    exact measurable_const

lemma measurable_tapeShift (c : X → ℕ) : Measurable (tapeShift c) := by
  refine measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun n => ?_
  exact (measurable_pi_apply (c x + n)).comp (measurable_pi_apply x)

lemma tapeTrunc_of_lt {c : X → ℕ} {y : X → ℕ → ℝ} {x : X} {n : ℕ} (h : n < c x) :
    tapeTrunc c y x n = y x n := by
  simp [tapeTrunc, h]

lemma tapeTrunc_tapeTrunc {c c' : X → ℕ} (h : ∀ x, c x ≤ c' x) (y : X → ℕ → ℝ) :
    tapeTrunc c (tapeTrunc c' y) = tapeTrunc c y := by
  funext x n
  unfold tapeTrunc
  by_cases h1 : n < c x
  · have h2 : n < c' x := lt_of_lt_of_le h1 (h x)
    simp [h1, h2]
  · simp [h1]

lemma comap_le_of_coord {Ω : Type*} [mΩ : MeasurableSpace Ω] (f : Ω → X → ℕ → ℝ)
    (h : ∀ x n, Measurable fun ω => f ω x n) : MeasurableSpace.comap f inferInstance ≤ mΩ :=
  (measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun n => h x n).comap_le

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_tapeOf {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n)) :
    Measurable (tapeOf Y) :=
  measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun n => hYm x n

/-- For jointly independent observations, the consumed block (entries below `c`) and the
segment starting at `c` are independent, for every deterministic count vector `c`. -/
lemma indepFun_trunc_shift (P : Measure Ω) {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n)) (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    (c : X → ℕ) :
    IndepFun (fun ω => tapeTrunc c (tapeOf Y ω)) (fun ω => tapeShift c (tapeOf Y ω)) P := by
  set m : X × ℕ → MeasurableSpace Ω := fun p => MeasurableSpace.comap (Y p.1 p.2) inferInstance
    with hmdef
  have hle : ∀ p, m p ≤ ‹MeasurableSpace Ω› := fun p => (hYm p.1 p.2).comap_le
  have hI : iIndep m P := hind.iIndep
  have hdisj : Disjoint {p : X × ℕ | p.2 < c p.1} {p : X × ℕ | c p.1 ≤ p.2} := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [Set.mem_ofPred_eq] at h1 h2
    omega
  have h := indep_iSup_of_disjoint hle hI hdisj
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right h ?_) ?_
  · refine @comap_le_of_coord X Ω (⨆ p ∈ {p : X × ℕ | c p.1 ≤ p.2}, m p) _ fun x n => ?_
    have h1 : m (x, c x + n) ≤ ⨆ p ∈ {p : X × ℕ | c p.1 ≤ p.2}, m p :=
      le_iSup₂_of_le (x, c x + n) (by simp) le_rfl
    exact (comap_measurable (Y x (c x + n))).mono h1 le_rfl
  · refine @comap_le_of_coord X Ω (⨆ p ∈ {p : X × ℕ | p.2 < c p.1}, m p) _ fun x n => ?_
    by_cases hn : n < c x
    · have h1 : m (x, n) ≤ ⨆ p ∈ {p : X × ℕ | p.2 < c p.1}, m p :=
        le_iSup₂_of_le (x, n) (by simpa using hn) le_rfl
      have h2 : (fun ω => tapeTrunc c (tapeOf Y ω) x n) = Y x n := by
        funext ω
        simp [tapeTrunc, tapeOf, hn]
      rw [h2]
      exact (comap_measurable (Y x n)).mono h1 le_rfl
    · have h2 : (fun ω => tapeTrunc c (tapeOf Y ω) x n) = fun _ => 0 := by
        funext ω
        simp [tapeTrunc, hn]
      rw [h2]
      exact measurable_const

/-- Freezing the consumed block at a deterministic count vector: the segment starting at `c`
is integrated out against its law. -/
lemma lintegral_block_freeze (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n)) (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    (c : X → ℕ) {H : (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ ω, H (tapeTrunc c (tapeOf Y ω), tapeShift c (tapeOf Y ω)) ∂P =
      ∫⁻ ω, ∫⁻ s, H (tapeTrunc c (tapeOf Y ω), s)
        ∂(P.map fun ω' => tapeShift c (tapeOf Y ω')) ∂P := by
  have hT : Measurable (fun ω => tapeTrunc c (tapeOf Y ω)) :=
    (measurable_tapeTrunc c).comp (measurable_tapeOf hYm)
  have hS : Measurable (fun ω => tapeShift c (tapeOf Y ω)) :=
    (measurable_tapeShift c).comp (measurable_tapeOf hYm)
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hT.aemeasurable hS.aemeasurable).mp
    (indepFun_trunc_shift P hYm hind c)
  have : IsProbabilityMeasure (P.map fun ω => tapeShift c (tapeOf Y ω)) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  calc ∫⁻ ω, H (tapeTrunc c (tapeOf Y ω), tapeShift c (tapeOf Y ω)) ∂P
      = ∫⁻ p, H p ∂(P.map fun ω => (tapeTrunc c (tapeOf Y ω), tapeShift c (tapeOf Y ω))) :=
        (lintegral_map hH (hT.prodMk hS)).symm
    _ = ∫⁻ p, H p ∂((P.map fun ω => tapeTrunc c (tapeOf Y ω)).prod
          (P.map fun ω => tapeShift c (tapeOf Y ω))) := by rw [hmap]
    _ = ∫⁻ t, ∫⁻ s, H (t, s) ∂(P.map fun ω => tapeShift c (tapeOf Y ω))
          ∂(P.map fun ω => tapeTrunc c (tapeOf Y ω)) := lintegral_prod _ hH.aemeasurable
    _ = ∫⁻ ω, ∫⁻ s, H (tapeTrunc c (tapeOf Y ω), s)
          ∂(P.map fun ω' => tapeShift c (tapeOf Y ω')) ∂P :=
        lintegral_map hH.lintegral_prod_right' hT

/-- **Adaptive-segment freshness.**  `Y x n` are jointly independent observations (over
`(x, n)`).  `N` is a count vector computed from the tape that only reads the observations it
counts: `N y = c` iff `N (tapeTrunc c y) = c` (a stopping rule for the per-type counts).  Then
for every family `G c` of jointly measurable nonnegative functions of the consumed block and of
the next segment,
`E[G_N(consumed block, segment starting at N)] = E[∫ G_N(consumed block, s) dπ_N(s)]`,
where `π_c` is the law of the segment starting at the deterministic counts `c` (equal to the
law of the whole tape when the observations of each type are identically distributed, see
`map_tapeShift_eq`).  The proof decomposes over the countably many values of `N`; on
`{N = c}` the segment is a fixed block of coordinates, independent of the consumed block. -/
theorem lintegral_adaptive_segment [Finite X] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    {N : (X → ℕ → ℝ) → X → ℕ} (hN : ∀ c, MeasurableSet {y | N y = c})
    (hNloc : ∀ y c, N (tapeTrunc c y) = c ↔ N y = c)
    {G : (X → ℕ) → (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ≥0∞} (hG : ∀ c, Measurable (G c)) :
    ∫⁻ ω, G (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω),
        tapeShift (N (tapeOf Y ω)) (tapeOf Y ω)) ∂P =
      ∫⁻ ω, ∫⁻ s, G (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω), s)
        ∂(P.map fun ω' => tapeShift (N (tapeOf Y ω)) (tapeOf Y ω')) ∂P := by
  classical
  set E : (X → ℕ) → Set Ω := fun c => {ω | N (tapeOf Y ω) = c} with hEdef
  have hE : ∀ c, MeasurableSet (E c) := fun c => measurable_tapeOf hYm (hN c)
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro c c' hcc
    refine Set.disjoint_left.mpr fun ω h1 h2 => hcc ?_
    exact h1.symm.trans h2
  have hU : ⋃ c, E c = Set.univ := Set.eq_univ_of_forall fun ω => Set.mem_iUnion.mpr ⟨_, rfl⟩
  have hsplit : ∀ f : Ω → ℝ≥0∞, ∫⁻ ω, f ω ∂P = ∑' c, ∫⁻ ω in E c, f ω ∂P := by
    intro f
    rw [← lintegral_iUnion hE hdisj, hU, Measure.restrict_univ]
  rw [hsplit, hsplit (fun ω => ∫⁻ s, G (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω), s)
        ∂(P.map fun ω' => tapeShift (N (tapeOf Y ω)) (tapeOf Y ω')))]
  refine tsum_congr fun c => ?_
  set H : (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ≥0∞ := fun p => if N p.1 = c then G c p else 0 with hH
  have hHm : Measurable H := Measurable.ite (measurable_fst (hN c)) (hG c) measurable_const
  have h1 : ∫⁻ ω in E c, G (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω),
        tapeShift (N (tapeOf Y ω)) (tapeOf Y ω)) ∂P =
      ∫⁻ ω, H (tapeTrunc c (tapeOf Y ω), tapeShift c (tapeOf Y ω)) ∂P := by
    rw [← lintegral_indicator (hE c)]
    refine lintegral_congr fun ω => ?_
    by_cases hω : N (tapeOf Y ω) = c
    · have hω' : ω ∈ E c := hω
      rw [Set.indicator_of_mem hω']
      simp only [hH, (hNloc _ c).mpr hω, ↓reduceIte, hω]
    · have hω' : ω ∉ E c := hω
      rw [Set.indicator_of_notMem hω']
      have : ¬ N (tapeTrunc c (tapeOf Y ω)) = c := fun h => hω ((hNloc _ c).mp h)
      simp only [hH, this, ↓reduceIte]
  have h2 : ∫⁻ ω in E c, ∫⁻ s, G (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω), s)
        ∂(P.map fun ω' => tapeShift (N (tapeOf Y ω)) (tapeOf Y ω')) ∂P =
      ∫⁻ ω, ∫⁻ s, H (tapeTrunc c (tapeOf Y ω), s)
        ∂(P.map fun ω' => tapeShift c (tapeOf Y ω')) ∂P := by
    rw [← lintegral_indicator (hE c)]
    refine lintegral_congr fun ω => ?_
    by_cases hω : N (tapeOf Y ω) = c
    · have hω' : ω ∈ E c := hω
      rw [Set.indicator_of_mem hω']
      simp only [hH, (hNloc _ c).mpr hω, ↓reduceIte, hω]
    · have hω' : ω ∉ E c := hω
      rw [Set.indicator_of_notMem hω']
      have : ¬ N (tapeTrunc c (tapeOf Y ω)) = c := fun h => hω ((hNloc _ c).mp h)
      simp only [hH, this, ↓reduceIte, lintegral_zero]
  rw [h1, h2]
  exact lintegral_block_freeze P hYm hind c hHm

/-- One-step inequality from adaptive-segment freshness: if every section of `Φ c` integrates
to at most one against the law of the segment starting at `c`, and the weight `g` only reads
the consumed observations, then multiplying by the factor of the next segment does not
increase the integral of `g`. -/
theorem lintegral_adaptive_segment_le [Finite X] (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    {N : (X → ℕ → ℝ) → X → ℕ} (hN : ∀ c, MeasurableSet {y | N y = c})
    (hNloc : ∀ y c, N (tapeTrunc c y) = c ↔ N y = c)
    {g : (X → ℕ → ℝ) → ℝ≥0∞} (hg : Measurable g)
    (hgloc : ∀ y, g (tapeTrunc (N y) y) = g y)
    {Φ : (X → ℕ) → (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ≥0∞} (hΦ : ∀ c, Measurable (Φ c))
    (hone : ∀ c t, ∫⁻ s, Φ c (t, s) ∂(P.map fun ω => tapeShift c (tapeOf Y ω)) ≤ 1) :
    ∫⁻ ω, g (tapeOf Y ω) * Φ (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω),
        tapeShift (N (tapeOf Y ω)) (tapeOf Y ω)) ∂P ≤ ∫⁻ ω, g (tapeOf Y ω) ∂P := by
  have hGm : ∀ c, Measurable (fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) => g p.1 * Φ c p) :=
    fun c => (hg.comp measurable_fst).mul (hΦ c)
  have h := lintegral_adaptive_segment P hYm hind hN hNloc hGm
  calc ∫⁻ ω, g (tapeOf Y ω) * Φ (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω),
        tapeShift (N (tapeOf Y ω)) (tapeOf Y ω)) ∂P
      = ∫⁻ ω, g (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω)) *
          Φ (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω),
            tapeShift (N (tapeOf Y ω)) (tapeOf Y ω)) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [hgloc]
    _ = _ := h
    _ ≤ ∫⁻ ω, g (tapeOf Y ω) ∂P := by
        refine lintegral_mono fun ω => ?_
        have hsec : Measurable fun s => Φ (N (tapeOf Y ω))
            (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω), s) :=
          (hΦ _).comp measurable_prodMk_left
        show ∫⁻ s, g (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω)) *
          Φ (N (tapeOf Y ω)) (tapeTrunc (N (tapeOf Y ω)) (tapeOf Y ω), s) ∂_ ≤ _
        rw [lintegral_const_mul _ hsec, hgloc]
        calc g (tapeOf Y ω) * _ ≤ g (tapeOf Y ω) * 1 := by gcongr; exact hone _ _
          _ = g (tapeOf Y ω) := mul_one _

/-- **The segment law does not depend on its position.**  If the observations of each type
are identically distributed, the segment starting at any deterministic count vector has the
law of the whole tape: the next segment is a batch of fresh i.i.d. draws. -/
theorem map_tapeShift_eq (P : Measure Ω) {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n)) (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    (hid : ∀ x n, P.map (Y x n) = P.map (Y x 0)) (c : X → ℕ) :
    P.map (fun ω => tapeShift c (tapeOf Y ω)) = P.map (tapeOf Y) := by
  have hcm : Measurable (Function.curry : (X × ℕ → ℝ) → X → ℕ → ℝ) :=
    measurable_pi_iff.mpr fun x => measurable_pi_iff.mpr fun n => measurable_pi_apply (x, n)
  have hinj : Function.Injective (fun p : X × ℕ => ((p.1, c p.1 + p.2) : X × ℕ)) := by
    rintro ⟨x, n⟩ ⟨x', n'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    have : n = n' := by omega
    rw [this]
  have hind2 : iIndepFun (fun p : X × ℕ => Y p.1 (c p.1 + p.2)) P := hind.precomp hinj
  have h1 := hind.map_fun_eq_infinitePi_map (fun p : X × ℕ => hYm p.1 p.2)
  have h2 := hind2.map_fun_eq_infinitePi_map (fun p : X × ℕ => hYm p.1 (c p.1 + p.2))
  have e : (fun p : X × ℕ => P.map (Y p.1 (c p.1 + p.2))) = fun p => P.map (Y p.1 p.2) :=
    funext fun p => (hid _ _).trans (hid _ _).symm
  rw [e, ← h1] at h2
  have e1 : (fun ω => tapeShift c (tapeOf Y ω)) =
      Function.curry ∘ (fun ω (p : X × ℕ) => Y p.1 (c p.1 + p.2) ω) := rfl
  have e2 : tapeOf Y = Function.curry ∘ (fun ω (p : X × ℕ) => Y p.1 p.2 ω) := rfl
  rw [e1, e2,
    ← Measure.map_map hcm (measurable_pi_iff.mpr fun p : X × ℕ => hYm p.1 (c p.1 + p.2)),
    ← Measure.map_map hcm (measurable_pi_iff.mpr fun p : X × ℕ => hYm p.1 p.2), h2]

end Tape

/-! ### Countable decompositions -/

section Countable

variable {α ι β : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι]

lemma measurable_comp_countable {D : α → ι} (hD : ∀ d, MeasurableSet {a | D a = d})
    {Ψ : ι → α → β} (hΨ : ∀ d, Measurable (Ψ d)) {f : α → β} (h : ∀ a, f a = Ψ (D a) a) :
    Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ d, {a | D a = d} ∩ Ψ d ⁻¹' s := by
    ext a
    constructor
    · intro ha
      refine Set.mem_iUnion.mpr ⟨D a, rfl, ?_⟩
      show Ψ (D a) a ∈ s
      rw [← h a]
      exact ha
    · intro ha
      obtain ⟨d, hd, hd2⟩ := Set.mem_iUnion.mp ha
      have hd' : D a = d := hd
      show f a ∈ s
      rw [h a, hd']
      exact hd2
  rw [this]
  exact MeasurableSet.iUnion fun d => (hD d).inter (hΨ d hs)

omit [MeasurableSpace β] in
lemma measurableSet_comp_countable {D : α → ι} (hD : ∀ d, MeasurableSet {a | D a = d})
    {Q : ι → α → Prop} (hQ : ∀ d, MeasurableSet {a | Q d a}) {p : α → Prop}
    (h : ∀ a, p a ↔ Q (D a) a) : MeasurableSet {a | p a} := by
  have : {a | p a} = ⋃ d, {a | D a = d} ∩ {a | Q d a} := by
    ext a
    constructor
    · intro ha
      exact Set.mem_iUnion.mpr ⟨D a, rfl, (h a).mp ha⟩
    · intro ha
      obtain ⟨d, hd, hd2⟩ := Set.mem_iUnion.mp ha
      have hd' : D a = d := hd
      have hd3 : Q d a := hd2
      exact (h a).mpr (hd' ▸ hd3)
  rw [this]
  exact MeasurableSet.iUnion fun d => (hD d).inter (hQ d)

end Countable

/-! ### Prefix statistics only read the prefix -/

lemma prefMean_congr {t t' : ℕ → ℝ} {n : ℕ} (h : ∀ i, i < n → t i = t' i) :
    prefMean t n = prefMean t' n := by
  unfold prefMean
  rw [Finset.sum_congr rfl fun i hi => h i (Finset.mem_range.mp hi)]

lemma prefVar_congr {t t' : ℕ → ℝ} {n : ℕ} (h : ∀ i, i < n → t i = t' i) :
    prefVar t n = prefVar t' n := by
  unfold prefVar
  rw [prefMean_congr h]
  rw [Finset.sum_congr rfl fun i hi => by rw [h i (Finset.mem_range.mp hi)]]

lemma predMean_congr {t t' : ℕ → ℝ} {n : ℕ} (h : ∀ i, i < n → t i = t' i) :
    predMean t n = predMean t' n := by
  unfold predMean
  rw [prefMean_congr h]

lemma predVar_congr (j : ℕ) {t t' : ℕ → ℝ} {n : ℕ} (h : ∀ i, i < n → t i = t' i) :
    predVar j t n = predVar j t' n := by
  unfold predVar
  rw [prefVar_congr h]

lemma predVar_pos {j : ℕ} (hj : 1 ≤ j) (t : ℕ → ℝ) (n : ℕ) : 0 < predVar j t n := by
  unfold predVar
  split_ifs
  · unfold truncVar
    have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    exact lt_min hj0 (lt_max_of_lt_left (inv_pos.mpr hj0))
  · exact one_pos

lemma batchDens_congr {X : Type*} [Fintype X] {r : X → ℕ} {t s : X → ℝ} {y y' : X → ℕ → ℝ}
    (h : ∀ x ℓ, ℓ < r x → y x ℓ = y' x ℓ) : batchDens r t s y = batchDens r t s y' := by
  unfold batchDens
  refine Finset.prod_congr rfl fun x _ => Finset.prod_congr rfl fun ℓ hℓ => ?_
  rw [h x ℓ (Finset.mem_range.mp hℓ)]

lemma measurable_predMean {X : Type*} (x : X) (n : ℕ) :
    Measurable fun y : X → ℕ → ℝ => predMean (y x) n := by
  unfold predMean prefMean
  by_cases h : 1 ≤ n
  · simp only [h, ↓reduceIte]
    exact (Finset.measurable_sum _ fun i _ =>
      (measurable_pi_apply i).comp (measurable_pi_apply x)).div_const _
  · simp only [h, ↓reduceIte]
    exact measurable_const

lemma measurable_predVar {X : Type*} (j : ℕ) (x : X) (n : ℕ) :
    Measurable fun y : X → ℕ → ℝ => predVar j (y x) n := by
  unfold predVar
  by_cases h : 2 ≤ n
  · simp only [h, ↓reduceIte]
    unfold truncVar prefVar prefMean
    refine measurable_const.min (measurable_const.max ?_)
    have hmean : Measurable fun y : X → ℕ → ℝ => (∑ i ∈ range n, y x i) / (n : ℝ) :=
      (Finset.measurable_sum _ fun i _ =>
        (measurable_pi_apply i).comp (measurable_pi_apply x)).div_const _
    exact (Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply i).comp (measurable_pi_apply x)).sub hmean).pow_const 2).div_const _
  · simp only [h, ↓reduceIte]
    exact measurable_const

lemma measurable_gaussianPDFReal_joint :
    Measurable fun q : ℝ × ℝ × ℝ => gaussianPDFReal q.1 q.2.1.toNNReal q.2.2 := by
  unfold gaussianPDFReal
  fun_prop

lemma measurable_batchDens_joint {X : Type*} [Fintype X] (r : X → ℕ) :
    Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) => batchDens r p.1 p.2.1 p.2.2 := by
  have hA : ∀ (x : X) (ℓ : ℕ), Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) =>
      ((p.1 x, p.2.1 x, p.2.2 x ℓ) : ℝ × ℝ × ℝ) := by
    intro x ℓ
    have a1 : Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) => p.1 x :=
      (measurable_pi_apply x).comp measurable_fst
    have a2 : Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) => p.2.1 x :=
      (measurable_pi_apply x).comp (measurable_fst.comp measurable_snd)
    have a3 : Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) => p.2.2 x ℓ :=
      (measurable_pi_apply ℓ).comp ((measurable_pi_apply x).comp
        (measurable_snd.comp measurable_snd))
    exact a1.prodMk (a2.prodMk a3)
  have hB : ∀ (x : X) (ℓ : ℕ), Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) =>
      gaussianPDFReal (p.1 x) (p.2.1 x).toNNReal (p.2.2 x ℓ) := by
    intro x ℓ
    have h := measurable_gaussianPDFReal_joint.comp (hA x ℓ)
    simpa only [Function.comp_def] using h
  unfold batchDens
  exact Finset.measurable_prod _ fun x _ => Finset.measurable_prod _ fun ℓ _ => hB x ℓ

/-- A batch with at least two observations of a type whose first two observations differ has
positive within-batch centered variance for that type. -/
lemma batchVar_pos_of_ne {X : Type*} {r : X → ℕ} {y : X → ℕ → ℝ} {x : X} (hr : 2 ≤ r x)
    (hne : y x 0 ≠ y x 1) : 0 < batchVar r y x := by
  unfold batchVar
  have hrpos : (0 : ℝ) < r x := by exact_mod_cast (by omega : 0 < r x)
  refine div_pos ?_ hrpos
  refine Finset.sum_pos' (fun ℓ _ => sq_nonneg _) ?_
  by_cases h0 : y x 0 = batchMean r y x
  · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
    have : y x 1 - batchMean r y x ≠ 0 := fun h => hne (h0.trans (sub_eq_zero.mp h).symm)
    positivity
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    have : y x 0 - batchMean r y x ≠ 0 := fun h => h0 (sub_eq_zero.mp h)
    positivity

/-! ### The tracker only reads the observations it has consumed -/

namespace Tracker

variable {X A Z U : Type*} (T : Tracker X A Z U)

lemma step_congr (j : ℕ) (s : TState X A) {y y' : X → ℕ → ℝ}
    (h : ∀ x n, n < s.cnt x → y x n = y' x n) : T.step y j s = T.step y' j s := by
  have e1 : (fun x => predMean (y x) (s.cnt x)) = fun x => predMean (y' x) (s.cnt x) :=
    funext fun x => predMean_congr fun i hi => h x i hi
  have e2 : (fun x => predVar (j + 1) (y x) (s.cnt x)) =
      fun x => predVar (j + 1) (y' x) (s.cnt x) :=
    funext fun x => predVar_congr (j + 1) fun i hi => h x i hi
  unfold step
  rw [e1, e2]

lemma cnt_mono (y : X → ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) (x : X) :
    (T.state y i).cnt x ≤ (T.state y j).cnt x := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    rw [T.cnt_succ y]
    omega

/-- The states up to batch `j + 1` are determined by the observations consumed by the end of
batch `j`. -/
lemma state_congr {y y' : X → ℕ → ℝ} (j : ℕ)
    (h : ∀ x n, n < (T.state y j).cnt x → y x n = y' x n) :
    ∀ k, k ≤ j + 1 → T.state y' k = T.state y k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    have e := ih (by omega)
    show T.step y' k (T.state y' k) = T.step y k (T.state y k)
    rw [e]
    exact (T.step_congr k (T.state y k) fun x n hn =>
      h x n (lt_of_lt_of_le hn (T.cnt_mono y (by omega) x))).symm

lemma state_tapeTrunc (i : ℕ) (y : X → ℕ → ℝ) :
    ∀ k, k ≤ i + 1 → T.state (tapeTrunc (T.state y i).cnt y) k = T.state y k :=
  T.state_congr i fun _ _ hn => (tapeTrunc_of_lt hn).symm

lemma cnt_tapeTrunc_iff (i : ℕ) (y : X → ℕ → ℝ) (c : X → ℕ) :
    (T.state (tapeTrunc c y) i).cnt = c ↔ (T.state y i).cnt = c := by
  constructor
  · intro h
    have := T.state_congr (y := tapeTrunc c y) (y' := y) i
      (fun x n hn => by rw [h] at hn; exact tapeTrunc_of_lt hn) i (by omega)
    rw [this]
    exact h
  · intro h
    have := T.state_tapeTrunc i y i (by omega)
    rw [h] at this
    rw [this]
    exact h

/-- The observations consumed by the end of batch `i`. -/
def stopTape (i : ℕ) (y : X → ℕ → ℝ) : X → ℕ → ℝ := tapeTrunc (T.state y i).cnt y

lemma stopTape_stopTape_succ (i : ℕ) (y : X → ℕ → ℝ) :
    T.stopTape i (T.stopTape (i + 1) y) = T.stopTape i y := by
  have h1 : T.state (T.stopTape (i + 1) y) i = T.state y i := by
    refine T.state_congr (y := y) i (fun x n hn => ?_) i (by omega)
    exact (tapeTrunc_of_lt (lt_of_lt_of_le hn (T.cnt_mono y (by omega) x))).symm
  unfold stopTape at h1 ⊢
  rw [h1]
  exact tapeTrunc_tapeTrunc (fun x => T.cnt_mono y (by omega) x) y

lemma stopTape_stopTape (i : ℕ) (y : X → ℕ → ℝ) :
    T.stopTape i (T.stopTape i y) = T.stopTape i y := by
  have h1 : T.state (T.stopTape i y) i = T.state y i := T.state_tapeTrunc i y i (by omega)
  unfold stopTape at h1 ⊢
  rw [h1]
  exact tapeTrunc_tapeTrunc (fun x => le_rfl) y

end Tracker

/-! ### Measurability of a run -/

section PairFiber

variable {α ι κ : Type*} [MeasurableSpace α]

lemma measurableSet_pair_fiber {D1 : α → ι} {D2 : α → κ}
    (h1 : ∀ d, MeasurableSet {a | D1 a = d}) (h2 : ∀ d, MeasurableSet {a | D2 a = d})
    (d : ι × κ) : MeasurableSet {a | (D1 a, D2 a) = d} := by
  have : {a | (D1 a, D2 a) = d} = {a | D1 a = d.1} ∩ {a | D2 a = d.2} := by
    ext a
    constructor
    · intro h
      have h' : (D1 a, D2 a) = d := h
      exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩
    · rintro ⟨h3, h4⟩
      have h3' : D1 a = d.1 := h3
      have h4' : D2 a = d.2 := h4
      exact Prod.ext h3' h4'
  rw [this]
  exact (h1 d.1).inter (h2 d.2)

end PairFiber

namespace Tracker

variable {X A Z U : Type*}

/-- Measurability of the oracles that drive the allocation: the design and its displayed score
are Borel functions of the estimates, the tie-breaking rule is a Borel function of the
displayed scores, and the rounding rule is a Borel function of the nominal design.  Nothing is
assumed about the certified bounds `qlo` and `Uhi`. -/
structure Meas (T : Tracker X A Z U) : Prop where
  design_meas : ∀ (k : ℕ) (a : A),
    Measurable fun p : (X → ℝ) × (X → ℝ) => T.design k p.1 p.2 a
  score_meas : ∀ (k : ℕ) (a : A),
    Measurable fun p : (X → ℝ) × (X → ℝ) => T.score k p.1 p.2 a
  pick_meas : ∀ a : A, MeasurableSet {f : A → ℝ | T.pick f = a}
  alloc_meas : ∀ (j : ℕ) (x : X), Measurable fun w : X → ℝ => T.alloc j w x

variable (T : Tracker X A Z U)

section StateMeas

variable [Fintype X] [Fintype A]

omit [Fintype X] in
lemma measurableSet_refInc (hm : T.Meas) (k : ℕ) (a0 a : A) :
    MeasurableSet {p : (X → ℝ) × (X → ℝ) | T.refInc k p.1 p.2 a0 = a} := by
  classical
  set C : Set ((X → ℝ) × (X → ℝ)) :=
    {p | ∀ b, T.score k p.1 p.2 b - T.score k p.1 p.2 a0 ≤ hyst k} with hCdef
  have hC : MeasurableSet C := by
    have : C = ⋂ b, {p : (X → ℝ) × (X → ℝ) |
        T.score k p.1 p.2 b - T.score k p.1 p.2 a0 ≤ hyst k} := by
      ext p
      simp [hCdef]
    rw [this]
    exact MeasurableSet.iInter fun b =>
      measurableSet_le ((hm.score_meas k b).sub (hm.score_meas k a0)) measurable_const
  have hP : MeasurableSet {p : (X → ℝ) × (X → ℝ) | T.pick (T.score k p.1 p.2) = a} :=
    (measurable_pi_iff.mpr fun b => hm.score_meas k b) (hm.pick_meas a)
  have : {p : (X → ℝ) × (X → ℝ) | T.refInc k p.1 p.2 a0 = a} =
      (C ∩ {_p | a0 = a}) ∪ (Cᶜ ∩ {p | T.pick (T.score k p.1 p.2) = a}) := by
    ext p
    by_cases h : ∀ b, T.score k p.1 p.2 b - T.score k p.1 p.2 a0 ≤ hyst k
    · have e : T.refInc k p.1 p.2 a0 = a0 := T.refInc_keep h
      have hp : p ∈ C := h
      constructor
      · intro h1
        have h1' : T.refInc k p.1 p.2 a0 = a := h1
        exact Or.inl ⟨hp, e.symm.trans h1'⟩
      · rintro (⟨-, h2⟩ | ⟨h2, -⟩)
        · have h2' : a0 = a := h2
          exact e.trans h2'
        · exact absurd hp h2
    · have e : T.refInc k p.1 p.2 a0 = T.pick (T.score k p.1 p.2) := by
        unfold refInc
        exact ite_eq_right h
      have hp : p ∉ C := h
      constructor
      · intro h1
        have h1' : T.refInc k p.1 p.2 a0 = a := h1
        exact Or.inr ⟨hp, e.symm.trans h1'⟩
      · rintro (⟨h2, -⟩ | ⟨-, h2⟩)
        · exact absurd h2 hp
        · have h2' : T.pick (T.score k p.1 p.2) = a := h2
          exact e.trans h2'
  rw [this]
  exact (hC.inter (MeasurableSet.const _)).union (hC.compl.inter hP)

omit [Fintype A] in
lemma measurableSet_alloc_add (hm : T.Meas) (j : ℕ) (c c' : X → ℕ) :
    MeasurableSet {w : X → ℝ | (fun x => c x + T.alloc j w x) = c'} := by
  have : {w : X → ℝ | (fun x => c x + T.alloc j w x) = c'} =
      ⋂ x, (fun w : X → ℝ => c x + T.alloc j w x) ⁻¹' {c' x} := by
    ext w
    constructor
    · intro h
      have h' : (fun x => c x + T.alloc j w x) = c' := h
      exact Set.mem_iInter.mpr fun x => congrFun h' x
    · intro h
      have h' := Set.mem_iInter.mp h
      exact funext fun x => h' x
  rw [this]
  exact MeasurableSet.iInter fun x =>
    (measurable_const.add (hm.alloc_meas j x)) (measurableSet_singleton _)

/-- The state of the tracker after each batch is a measurable function of the tape: the
counts and the incumbent have measurable level sets and the nominal design is measurable. -/
theorem state_meas (hm : T.Meas) (j : ℕ) :
    (∀ (c : X → ℕ) (a : A),
      MeasurableSet {y : X → ℕ → ℝ | (T.state y j).cnt = c ∧ (T.state y j).inc = a}) ∧
      Measurable (fun y : X → ℕ → ℝ => (T.state y j).w) := by
  classical
  induction j with
  | zero =>
    refine ⟨fun c a => ?_, ?_⟩
    · have : {y : X → ℕ → ℝ | (T.state y 0).cnt = c ∧ (T.state y 0).inc = a} =
          {_y | (fun _ : X => (0 : ℕ)) = c ∧ T.init = a} := rfl
      rw [this]
      exact MeasurableSet.const _
    · exact measurable_const
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcnt : ∀ c, MeasurableSet {y : X → ℕ → ℝ | (T.state y j).cnt = c} := by
      intro c
      have : {y : X → ℕ → ℝ | (T.state y j).cnt = c} =
          ⋃ a, {y | (T.state y j).cnt = c ∧ (T.state y j).inc = a} := by
        ext y
        constructor
        · intro h
          exact Set.mem_iUnion.mpr ⟨(T.state y j).inc, h, rfl⟩
        · intro h
          obtain ⟨a, h1, -⟩ := Set.mem_iUnion.mp h
          exact h1
      rw [this]
      exact MeasurableSet.iUnion fun a => ih1 c a
    have hinc : ∀ a, MeasurableSet {y : X → ℕ → ℝ | (T.state y j).inc = a} := by
      intro a
      have : {y : X → ℕ → ℝ | (T.state y j).inc = a} =
          ⋃ c, {y | (T.state y j).cnt = c ∧ (T.state y j).inc = a} := by
        ext y
        constructor
        · intro h
          exact Set.mem_iUnion.mpr ⟨(T.state y j).cnt, rfl, h⟩
        · intro h
          obtain ⟨c, -, h1⟩ := Set.mem_iUnion.mp h
          exact h1
      rw [this]
      exact MeasurableSet.iUnion fun c => ih1 c a
    have hDm := measurableSet_pair_fiber hcnt hinc
    have hmh : ∀ c : X → ℕ, Measurable fun y : X → ℕ → ℝ =>
        ((fun x => predMean (y x) (c x), fun x => predVar (j + 1) (y x) (c x)) :
          (X → ℝ) × (X → ℝ)) := fun c =>
      (measurable_pi_iff.mpr fun x => measurable_predMean x (c x)).prodMk
        (measurable_pi_iff.mpr fun x => measurable_predVar (j + 1) x (c x))
    have hcntS : ∀ y : X → ℕ → ℝ, (T.state y (j + 1)).cnt =
        fun x => (T.state y j).cnt x + T.alloc (j + 1) (T.state y (j + 1)).w x := fun y =>
      funext fun x => T.step_cnt y j (T.state y j) x
    by_cases hr : 4 ^ Nat.log 4 (j + 1) = j + 1
    · set k := Nat.log 4 (j + 1) with hk
      have hincS : ∀ y : X → ℕ → ℝ, (T.state y (j + 1)).inc =
          T.refInc k (fun x => predMean (y x) ((T.state y j).cnt x))
            (fun x => predVar (j + 1) (y x) ((T.state y j).cnt x)) (T.state y j).inc :=
        fun y => T.step_refresh_inc y (T.state y j) hr
      have hwS : ∀ y : X → ℕ → ℝ, (T.state y (j + 1)).w =
          T.design k (fun x => predMean (y x) ((T.state y j).cnt x))
            (fun x => predVar (j + 1) (y x) ((T.state y j).cnt x)) (T.state y (j + 1)).inc :=
        fun y => T.step_refresh_w y (T.state y j) hr
      have hEa : ∀ a, MeasurableSet {y : X → ℕ → ℝ | (T.state y (j + 1)).inc = a} := by
        intro a
        refine measurableSet_comp_countable hDm
          (Q := fun d y => T.refInc k (fun x => predMean (y x) (d.1 x))
            (fun x => predVar (j + 1) (y x) (d.1 x)) d.2 = a)
          (fun d => (hmh d.1) (T.measurableSet_refInc hm k d.2 a)) (fun y => ?_)
        rw [hincS y]
      have hD'm := measurableSet_pair_fiber hcnt hEa
      have hwm : Measurable fun y : X → ℕ → ℝ => (T.state y (j + 1)).w := by
        refine measurable_comp_countable hD'm
          (Ψ := fun d y => T.design k (fun x => predMean (y x) (d.1 x))
            (fun x => predVar (j + 1) (y x) (d.1 x)) d.2)
          (fun d => ?_) (fun y => hwS y)
        have h := (hm.design_meas k d.2).comp (hmh d.1)
        simpa only [Function.comp_def] using h
      refine ⟨fun c' a => ?_, hwm⟩
      have hc' : MeasurableSet {y : X → ℕ → ℝ | (T.state y (j + 1)).cnt = c'} := by
        refine measurableSet_comp_countable hcnt
          (Q := fun c y => (fun x => c x + T.alloc (j + 1) (T.state y (j + 1)).w x) = c')
          (fun c => hwm (T.measurableSet_alloc_add hm (j + 1) c c')) (fun y => ?_)
        rw [hcntS y]
      exact hc'.inter (hEa a)
    · have hnr := fun y : X → ℕ → ℝ => T.step_not_refresh y (T.state y j) hr
      have hw : ∀ y : X → ℕ → ℝ, (T.state y (j + 1)).w = (T.state y j).w := fun y => (hnr y).2
      have hi : ∀ y : X → ℕ → ℝ, (T.state y (j + 1)).inc = (T.state y j).inc :=
        fun y => (hnr y).1
      have hwm : Measurable fun y : X → ℕ → ℝ => (T.state y (j + 1)).w := by
        have : (fun y : X → ℕ → ℝ => (T.state y (j + 1)).w) = fun y => (T.state y j).w :=
          funext hw
        rw [this]
        exact ih2
      refine ⟨fun c' a => ?_, hwm⟩
      refine measurableSet_comp_countable hDm
        (Q := fun d y => (fun x => d.1 x + T.alloc (j + 1) (T.state y j).w x) = c' ∧ d.2 = a)
        (fun d => (ih2 (T.measurableSet_alloc_add hm (j + 1) d.1 c')).inter
          (MeasurableSet.const _)) (fun y => ?_)
      rw [hcntS y, hi y, hw y]

lemma measurableSet_cnt (hm : T.Meas) (j : ℕ) (c : X → ℕ) :
    MeasurableSet {y : X → ℕ → ℝ | (T.state y j).cnt = c} := by
  have : {y : X → ℕ → ℝ | (T.state y j).cnt = c} =
      ⋃ a, {y | (T.state y j).cnt = c ∧ (T.state y j).inc = a} := by
    ext y
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨(T.state y j).inc, h, rfl⟩
    · intro h
      obtain ⟨a, h1, -⟩ := Set.mem_iUnion.mp h
      exact h1
  rw [this]
  exact MeasurableSet.iUnion fun a => (T.state_meas hm j).1 c a

lemma measurableSet_sel (hm : T.Meas) (j : ℕ) (a : A) :
    MeasurableSet {y : X → ℕ → ℝ | T.sel y j = a} := by
  have : {y : X → ℕ → ℝ | T.sel y j = a} =
      ⋃ c, {y | (T.state y j).cnt = c ∧ (T.state y j).inc = a} := by
    ext y
    constructor
    · intro h
      exact Set.mem_iUnion.mpr ⟨(T.state y j).cnt, rfl, h⟩
    · intro h
      obtain ⟨c, -, h1⟩ := Set.mem_iUnion.mp h
      exact h1
  rw [this]
  exact MeasurableSet.iUnion fun c => (T.state_meas hm j).1 c a

lemma measurableSet_rr (hm : T.Meas) (j : ℕ) (r : X → ℕ) :
    MeasurableSet {y : X → ℕ → ℝ | T.rr y j = r} := by
  have h := (T.state_meas hm j).2 (T.measurableSet_alloc_add hm j (fun _ => 0) r)
  have : {y : X → ℕ → ℝ | T.rr y j = r} =
      (fun y : X → ℕ → ℝ => (T.state y j).w) ⁻¹'
        {w : X → ℝ | (fun x => (fun _ => 0) x + T.alloc j w x) = r} := by
    ext y
    constructor
    · intro h1
      have h1' : T.rr y j = r := h1
      show (fun x => 0 + T.alloc j (T.state y j).w x) = r
      rw [← h1']
      funext x
      simp [rr, wnom]
    · intro h1
      have h1' : (fun x => 0 + T.alloc j (T.state y j).w x) = r := h1
      show T.rr y j = r
      rw [← h1']
      funext x
      simp [rr, wnom]
  rw [this]
  exact h

lemma measurable_stopTape (hm : T.Meas) (i : ℕ) : Measurable (T.stopTape i) :=
  measurable_comp_countable (T.measurableSet_cnt hm i) (Ψ := fun c y => tapeTrunc c y)
    (fun c => measurable_tapeTrunc c) (fun _ => rfl)

end StateMeas

/-! ### The likelihood-ratio wealth that dominates the tracker's wealth -/

section Ideal

variable [Fintype X]

/-- The exact half-cash factor of batch `i`: the plug-in Gaussian predictor density over the
batch density with query means `mean` and variances `v`. -/
def idealF (y : X → ℕ → ℝ) (mean v : X → ℝ) (i : ℕ) : ℝ :=
  halfCash (batchDens (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i))
    (batchDens (T.rr y i) mean v (T.yb y i))

lemma idealF_nonneg (y : X → ℕ → ℝ) (mean v : X → ℝ) (i : ℕ) : 0 ≤ T.idealF y mean v i := by
  have := halfCash_ge_half
    (batchDens_nonneg (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i))
    (batchDens_nonneg (T.rr y i) mean v (T.yb y i))
  unfold idealF
  linarith

lemma idealF_congr {y y' : X → ℕ → ℝ} (mean v : X → ℝ) (k : ℕ)
    (hst : ∀ m, m ≤ k + 1 → T.state y' m = T.state y m)
    (hag : ∀ x n, n < (T.state y (k + 1)).cnt x → y' x n = y x n) :
    T.idealF y' mean v (k + 1) = T.idealF y mean v (k + 1) := by
  have hrr : T.rr y' (k + 1) = T.rr y (k + 1) := by
    unfold rr wnom
    rw [hst (k + 1) le_rfl]
  have hcB : T.cntB y' (k + 1) = T.cntB y (k + 1) := by
    unfold cntB
    rw [hst _ (by omega)]
  have hcB2 : ∀ x, T.cntB y (k + 1) x ≤ (T.state y (k + 1)).cnt x :=
    fun x => T.cnt_mono y (by omega) x
  have hmu : T.muh y' (k + 1) = T.muh y (k + 1) := by
    unfold muh
    rw [hcB]
    exact funext fun x => predMean_congr fun i hi => hag x i (lt_of_lt_of_le hi (hcB2 x))
  have hvh : T.vhh y' (k + 1) = T.vhh y (k + 1) := by
    unfold vhh
    rw [hcB]
    exact funext fun x => predVar_congr (k + 1) fun i hi =>
      hag x i (lt_of_lt_of_le hi (hcB2 x))
  have hyb : ∀ x ℓ, ℓ < T.rr y (k + 1) x → T.yb y' (k + 1) x ℓ = T.yb y (k + 1) x ℓ := by
    intro x ℓ hℓ
    unfold yb
    rw [hcB]
    refine hag x _ ?_
    have h1 := T.cnt_succ y k x
    have e : T.cntB y (k + 1) x = (T.state y k).cnt x := rfl
    omega
  unfold idealF
  rw [hrr, hmu, hvh, batchDens_congr hyb, batchDens_congr (t := mean) hyb]

variable [DecidableEq A]

/-- The action-local wealth built from the exact factors `idealF`. -/
def idealWealth (y : X → ℕ → ℝ) (mean v : X → ℝ) (a : A) (j : ℕ) : ℝ :=
  localWealth (fun i => T.idealF y mean v i) (T.sel y) a j

lemma idealWealth_nonneg (y : X → ℕ → ℝ) (mean v : X → ℝ) (a : A) (j : ℕ) :
    0 ≤ T.idealWealth y mean v a j :=
  localWealth_nonneg (fun i => T.idealF_nonneg y mean v i) j

lemma idealWealth_congr {y y' : X → ℕ → ℝ} (mean v : X → ℝ) (a : A) (i : ℕ)
    (hst : ∀ m, m ≤ i → T.state y' m = T.state y m)
    (hag : ∀ x n, n < (T.state y i).cnt x → y' x n = y x n) :
    T.idealWealth y' mean v a i = T.idealWealth y mean v a i := by
  unfold idealWealth localWealth
  refine Finset.prod_congr rfl fun l hl => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have hsel : T.sel y' (k + 1) = T.sel y (k + 1) := by
    unfold sel
    rw [hst _ h2]
  show (if T.sel y' (k + 1) = a then T.idealF y' mean v (k + 1) else 1) =
    (if T.sel y (k + 1) = a then T.idealF y mean v (k + 1) else 1)
  rw [hsel, T.idealF_congr mean v k (fun m hm => hst m (by omega))
    (fun x n hn => hag x n (lt_of_lt_of_le hn (T.cnt_mono y h2 x)))]

lemma idealWealth_stopTape (y : X → ℕ → ℝ) (mean v : X → ℝ) (a : A) (i : ℕ) :
    T.idealWealth (T.stopTape i y) mean v a i = T.idealWealth y mean v a i :=
  T.idealWealth_congr mean v a i (fun m hm => T.state_tapeTrunc i y m (by omega))
    (fun _ _ hn => tapeTrunc_of_lt hn)

/-- **The tracker's wealth is dominated by the likelihood-ratio wealth.**  If the true
parameter `θ` lies in the component null `H a z`, the true variances are positive and no batch
is degenerate, then on every tape `E^loc_{a,z}(j) ≤ ∏ ½ (1 + q_i / p_i)`, the product over the
batches at which `a` is selected, with `q_i` the plug-in predictor density and `p_i` the true
batch density.  Only the two outward enclosures of the contract are used. -/
lemma wealth_le_idealWealth (hc : T.Contract) (y : X → ℕ → ℝ) {θ : U} {v : X → ℝ}
    (hv : ∀ x, 0 < v x) {a : A} {z : Z} (hz : z ∈ T.J a) (hθ : θ ∈ T.H a z)
    (hnd : ∀ i, 1 ≤ i → ∀ x, 0 < batchVar (T.rr y i) (T.yb y i) x) (j : ℕ) :
    T.wealth y a z j ≤ T.idealWealth y (fun x => T.pred x θ) v a j := by
  unfold wealth idealWealth localWealth
  refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i hi => ?_)
  · split_ifs
    · have := halfCash_ge_half
        (hc.qlo_nonneg i (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i))
        (hc.Uhi_nonneg a z i (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i))
      unfold qloV UhiV
      linarith
    · exact zero_le_one
  · have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    split_ifs with h
    · have hvh : ∀ x, 0 < T.vhh y i x := fun x => predVar_pos hi1 _ _
      have hnd' := hnd i hi1
      have hp : 0 < batchDens (T.rr y i) (fun x => T.pred x θ) v (T.yb y i) :=
        batchDens_pos _ _ hv _
      have hU : batchDens (T.rr y i) (fun x => T.pred x θ) v (T.yb y i) ≤ T.UhiV y a z i :=
        (batchDens_le_nullEnv hnd' hθ hv).trans (hc.Uhi_ge a z i _ _ _ _ hz hnd')
      have hq : T.qloV y i ≤ batchDens (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i) :=
        hc.qlo_le i (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i) hvh
      have hle : T.qloV y i / T.UhiV y a z i ≤
          batchDens (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i) /
            batchDens (T.rr y i) (fun x => T.pred x θ) v (T.yb y i) :=
        div_le_div₀ (batchDens_nonneg _ _ _ _) hq hp hU
      unfold idealF halfCash
      linarith
    · exact le_rfl

variable [Fintype A]

omit [DecidableEq A] in
lemma measurable_idealF (hm : T.Meas) (mean v : X → ℝ) (k : ℕ) :
    Measurable fun y : X → ℕ → ℝ => T.idealF y mean v (k + 1) := by
  refine measurable_comp_countable
    (measurableSet_pair_fiber (T.measurableSet_cnt hm k) (T.measurableSet_rr hm (k + 1)))
    (Ψ := fun d y => halfCash
      (batchDens d.2 (fun x => predMean (y x) (d.1 x)) (fun x => predVar (k + 1) (y x) (d.1 x))
        (tapeShift d.1 y))
      (batchDens d.2 mean v (tapeShift d.1 y))) (fun d => ?_) (fun y => rfl)
  have hq : Measurable fun y : X → ℕ → ℝ => batchDens d.2 (fun x => predMean (y x) (d.1 x))
      (fun x => predVar (k + 1) (y x) (d.1 x)) (tapeShift d.1 y) := by
    have h := (measurable_batchDens_joint d.2).comp
      ((measurable_pi_iff.mpr fun x => measurable_predMean x (d.1 x)).prodMk
        ((measurable_pi_iff.mpr fun x => measurable_predVar (k + 1) x (d.1 x)).prodMk
          (measurable_tapeShift d.1)))
    simpa only [Function.comp_def] using h
  have hU : Measurable fun y : X → ℕ → ℝ => batchDens d.2 mean v (tapeShift d.1 y) := by
    have h := (measurable_batchDens d.2 mean v).comp (measurable_tapeShift d.1)
    simpa only [Function.comp_def] using h
  exact measurable_halfCash hq hU

lemma measurable_idealWealth (hm : T.Meas) (mean v : X → ℝ) (a : A) (j : ℕ) :
    Measurable fun y : X → ℕ → ℝ => T.idealWealth y mean v a j := by
  unfold idealWealth localWealth
  refine Finset.measurable_prod _ fun l hl => ?_
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Finset.mem_Icc.mp hl).1; omega⟩
  exact Measurable.ite (T.measurableSet_sel hm (k + 1) a) (T.measurable_idealF hm mean v k)
    measurable_const

/-- The exact factor of batch `k + 1` as a function of the consumed block (first component,
with the counts frozen at `c`) and of the next segment (second component). -/
def frozenF (mean v : X → ℝ) (k : ℕ) (a : A) (c : X → ℕ)
    (p : (X → ℕ → ℝ) × (X → ℕ → ℝ)) : ℝ :=
  if T.sel p.1 (k + 1) = a then
    halfCash (batchDens (T.rr p.1 (k + 1)) (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2)
      (batchDens (T.rr p.1 (k + 1)) mean v p.2)
  else 1

omit [Fintype A] in
lemma frozenF_nonneg (mean v : X → ℝ) (k : ℕ) (a : A) (c : X → ℕ)
    (p : (X → ℕ → ℝ) × (X → ℕ → ℝ)) : 0 ≤ T.frozenF mean v k a c p := by
  unfold frozenF
  split_ifs
  · have := halfCash_ge_half
      (batchDens_nonneg (T.rr p.1 (k + 1)) (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2)
      (batchDens_nonneg (T.rr p.1 (k + 1)) mean v p.2)
    linarith
  · exact zero_le_one

lemma measurable_frozenF (hm : T.Meas) (mean v : X → ℝ) (k : ℕ) (a : A) (c : X → ℕ) :
    Measurable (T.frozenF mean v k a c) := by
  have hbody : Measurable fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) =>
      halfCash (batchDens (T.rr p.1 (k + 1)) (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2)
      (batchDens (T.rr p.1 (k + 1)) mean v p.2) := by
    refine measurable_comp_countable (D := fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) => T.rr p.1 (k + 1))
      (fun r => measurable_fst (T.measurableSet_rr hm (k + 1) r))
      (Ψ := fun r p => halfCash (batchDens r (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2) (batchDens r mean v p.2))
      (fun r => ?_) (fun p => rfl)
    have hq : Measurable fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) =>
        batchDens r (fun x => predMean (p.1 x) (c x))
          (fun x => predVar (k + 1) (p.1 x) (c x)) p.2 := by
      have h := (measurable_batchDens_joint r).comp
        (((measurable_pi_iff.mpr fun x => measurable_predMean x (c x)).comp
            (measurable_fst : Measurable (Prod.fst : (X → ℕ → ℝ) × (X → ℕ → ℝ) → X → ℕ → ℝ))).prodMk
          (((measurable_pi_iff.mpr fun x => measurable_predVar (k + 1) x (c x)).comp
            (measurable_fst : Measurable (Prod.fst : (X → ℕ → ℝ) × (X → ℕ → ℝ) → X → ℕ → ℝ))).prodMk measurable_snd))
      simpa only [Function.comp_def] using h
    have hU : Measurable fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) => batchDens r mean v p.2 := by
      have h := (measurable_batchDens r mean v).comp
        (measurable_snd : Measurable (Prod.snd : (X → ℕ → ℝ) × (X → ℕ → ℝ) → X → ℕ → ℝ))
      simpa only [Function.comp_def] using h
    exact measurable_halfCash hq hU
  exact Measurable.ite (measurable_fst (T.measurableSet_sel hm (k + 1) a)) hbody measurable_const

omit [Fintype A] in
/-- On the event that the counts after batch `k` are `c`, the factor of batch `k + 1` is the
frozen factor evaluated at the consumed block and at the segment starting at `c`. -/
lemma frozenF_eq (mean v : X → ℝ) (k : ℕ) (a : A) (y : X → ℕ → ℝ) :
    T.frozenF mean v k a (T.state y k).cnt
        (tapeTrunc (T.state y k).cnt y, tapeShift (T.state y k).cnt y) =
      if T.sel y (k + 1) = a then T.idealF y mean v (k + 1) else 1 := by
  have hst := T.state_tapeTrunc k y
  have hsel : T.sel (tapeTrunc (T.state y k).cnt y) (k + 1) = T.sel y (k + 1) := by
    unfold sel
    rw [hst _ le_rfl]
  have hrr : T.rr (tapeTrunc (T.state y k).cnt y) (k + 1) = T.rr y (k + 1) := by
    unfold rr wnom
    rw [hst _ le_rfl]
  have hpm : (fun x => predMean (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x)) =
      T.muh y (k + 1) :=
    funext fun x => predMean_congr fun i hi => tapeTrunc_of_lt hi
  have hpv : (fun x => predVar (k + 1) (tapeTrunc (T.state y k).cnt y x)
      ((T.state y k).cnt x)) = T.vhh y (k + 1) :=
    funext fun x => predVar_congr (k + 1) fun i hi => tapeTrunc_of_lt hi
  show (if T.sel (tapeTrunc (T.state y k).cnt y) (k + 1) = a then
      halfCash (batchDens (T.rr (tapeTrunc (T.state y k).cnt y) (k + 1))
        (fun x => predMean (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x))
        (fun x => predVar (k + 1) (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x))
        (tapeShift (T.state y k).cnt y))
      (batchDens (T.rr (tapeTrunc (T.state y k).cnt y) (k + 1)) mean v
        (tapeShift (T.state y k).cnt y)) else 1) = _
  rw [hsel, hrr, hpm, hpv]
  rfl

end Ideal

end Tracker

/-! ### Supermartingale and coverage for the tracker -/

section Adjacent

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [Countable X]

omit [Countable X] in
lemma shift_injective (c : X → ℕ) :
    Function.Injective (fun p : X × ℕ => ((p.1, c p.1 + p.2) : X × ℕ)) := by
  rintro ⟨x, n⟩ ⟨x', n'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have : n = n' := by omega
  rw [this]

/-- Almost surely no two consecutive observations of a type coincide. -/
lemma measure_adjacent_eq_zero (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n)) (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    {mean v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (mean x) (v x).toNNReal) P) :
    P {ω | ∃ x n, Y x n ω = Y x (n + 1) ω} = 0 := by
  have : {ω | ∃ x n, Y x n ω = Y x (n + 1) ω} = ⋃ x, ⋃ n, {ω | Y x n ω = Y x (n + 1) ω} := by
    ext ω
    constructor
    · rintro ⟨x, n, h⟩
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨n, h⟩⟩
    · intro h
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact ⟨x, n, hn⟩
  rw [this]
  refine measure_iUnion_null fun x => measure_iUnion_null fun n => ?_
  have hne : ((x, n) : X × ℕ) ≠ (x, n + 1) := by simp
  have hI : IndepFun (Y x n) (Y x (n + 1)) P :=
    hind.indepFun (i := ((x, n) : X × ℕ)) (j := ((x, n + 1) : X × ℕ)) hne
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map (hYm x n).aemeasurable
    (hYm x (n + 1)).aemeasurable).mp hI
  rw [(hlaw x n).map_eq, (hlaw x (n + 1)).map_eq] at hmap
  have hD : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have h1 : P {ω | Y x n ω = Y x (n + 1) ω} =
      (P.map fun ω => (Y x n ω, Y x (n + 1) ω)) {p : ℝ × ℝ | p.1 = p.2} := by
    rw [Measure.map_apply ((hYm x n).prodMk (hYm x (n + 1))) hD]
    rfl
  rw [h1, hmap, Measure.prod_apply hD]
  have := nullSingletonClass_gaussianReal (μ := mean x) (v := (v x).toNNReal)
    (toNNReal_ne_zero_of_pos (hv x))
  have h2 : ∀ a : ℝ, Prod.mk a ⁻¹' {p : ℝ × ℝ | p.1 = p.2} = {a} := by
    intro a
    ext b
    constructor
    · intro h
      have h' : a = b := h
      exact h'.symm
    · intro h
      have h' : b = a := h
      exact h'.symm
  simp only [h2, measure_singleton, lintegral_zero]

end Adjacent

namespace Tracker

section Coverage

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Fintype A]
  [DecidableEq A] (T : Tracker X A Z U)

omit [Fintype A] in
/-- Every section of the frozen factor integrates to at most one against the law of the next
segment: the one-step likelihood-ratio identity for a Gaussian batch of frozen sizes. -/
lemma lintegral_frozenF_le_one (P : Measure Ω) [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ}
    (hYm : ∀ x n, Measurable (Y x n)) (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    {mean v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (mean x) (v x).toNNReal) P)
    (k : ℕ) (a : A) (c : X → ℕ) (t : X → ℕ → ℝ) :
    ∫⁻ s, ENNReal.ofReal (T.frozenF mean v k a c (t, s))
      ∂(P.map fun ω => tapeShift c (tapeOf Y ω)) ≤ 1 := by
  have hS : Measurable (fun ω => tapeShift c (tapeOf Y ω)) :=
    (measurable_tapeShift c).comp (measurable_tapeOf hYm)
  have : IsProbabilityMeasure (P.map fun ω => tapeShift c (tapeOf Y ω)) :=
    (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
  have hdef : ∀ s, T.frozenF mean v k a c (t, s) =
      if T.sel t (k + 1) = a then
        halfCash (batchDens (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
            (fun x => predVar (k + 1) (t x) (c x)) s)
          (batchDens (T.rr t (k + 1)) mean v s)
      else 1 := fun s => rfl
  by_cases h : T.sel t (k + 1) = a
  · have hvh : ∀ x, 0 < predVar (k + 1) (t x) (c x) := fun x => predVar_pos (by omega) _ _
    have hm1 : Measurable fun s : X → ℕ → ℝ => ENNReal.ofReal
        (batchDens (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
            (fun x => predVar (k + 1) (t x) (c x)) s /
          batchDens (T.rr t (k + 1)) mean v s) :=
      ENNReal.measurable_ofReal.comp
        ((measurable_batchDens _ _ _).div (measurable_batchDens _ _ _))
    have hbound : ∀ s, ENNReal.ofReal (T.frozenF mean v k a c (t, s)) ≤
        ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) * ENNReal.ofReal
          (batchDens (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
              (fun x => predVar (k + 1) (t x) (c x)) s /
            batchDens (T.rr t (k + 1)) mean v s) := by
      intro s
      have hp : 0 < batchDens (T.rr t (k + 1)) mean v s := batchDens_pos _ _ hv s
      have hr0 : 0 ≤ batchDens (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
            (fun x => predVar (k + 1) (t x) (c x)) s /
          batchDens (T.rr t (k + 1)) mean v s :=
        div_nonneg (batchDens_nonneg _ _ _ _) hp.le
      rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num)
        (by positivity), hdef s, ite_eq_left h]
      apply ENNReal.ofReal_le_ofReal
      unfold halfCash
      linarith
    have hind2 : iIndepFun (fun (p : X × ℕ) ω => tapeShift c (tapeOf Y ω) p.1 p.2) P :=
      hind.precomp (shift_injective c)
    have hlaw2 : ∀ x ℓ, HasLaw (fun ω => tapeShift c (tapeOf Y ω) x ℓ)
        (gaussianReal (mean x) (v x).toNNReal) P := fun x ℓ => hlaw x (c x + ℓ)
    refine (lintegral_mono hbound).trans (le_of_eq ?_)
    rw [lintegral_add_left measurable_const, lintegral_const_mul _ hm1, lintegral_const,
      lintegral_map hm1 hS,
      lintegral_batch_ratio_eq_one P (Y := fun ω => tapeShift c (tapeOf Y ω)) hv hind2 hlaw2
        (T.rr t (k + 1)) (fun x => predMean (t x) (c x)) hvh, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  · have hΦ : ∀ s, T.frozenF mean v k a c (t, s) = 1 := fun s => by rw [hdef s, ite_eq_right h]
    simp [hΦ]

/-- The filtration generated by the observations the tracker has consumed: `ℱ_i` is generated
by the tape stopped at the per-type counts after batch `i`. -/
def obsFiltration (hm : T.Meas) {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n)) :
    Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq i := MeasurableSpace.comap (fun ω => T.stopTape i (tapeOf Y ω)) inferInstance
  mono' := by
    refine monotone_nat_of_le_succ fun i => ?_
    have hfun : (fun ω => T.stopTape i (tapeOf Y ω)) =
        (T.stopTape i) ∘ (fun ω => T.stopTape (i + 1) (tapeOf Y ω)) := by
      funext ω
      exact (T.stopTape_stopTape_succ i (tapeOf Y ω)).symm
    rw [hfun, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (T.measurable_stopTape hm i).comap_le
  le' i := ((T.measurable_stopTape hm i).comp (measurable_tapeOf hYm)).comap_le

/-- **Supermartingale criterion for an action-local wealth on intrinsic tapes.**  `F i y` is
the factor of batch `i` on the tape `y`, and `G k c` represents the factor of batch `k + 1` as
a jointly measurable function of the consumed block (counts frozen at `c`) and of the next
segment.  If every section of `G k c` integrates to at most one against the law of the segment
starting at `c`, and the wealth is measurable and only reads consumed observations, then the
action-local wealth is a supermartingale for the filtration of consumed observations.  The
conditional-expectation inequality comes from adaptive-segment freshness
(`lintegral_adaptive_segment_le`). -/
theorem factorWealth_supermartingale (hm : T.Meas) (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (a : A)
    (F : ℕ → (X → ℕ → ℝ) → ℝ) (G : ℕ → (X → ℕ) → (X → ℕ → ℝ) × (X → ℕ → ℝ) → ℝ)
    (hF0 : ∀ i y, 0 ≤ F i y)
    (hWm : ∀ j, Measurable fun y => localWealth (fun i => F i y) (T.sel y) a j)
    (hWloc : ∀ j y, localWealth (fun i => F i (T.stopTape j y)) (T.sel (T.stopTape j y)) a j =
      localWealth (fun i => F i y) (T.sel y) a j)
    (hGm : ∀ k c, Measurable (G k c))
    (hGeq : ∀ k y, G k (T.state y k).cnt
        (tapeTrunc (T.state y k).cnt y, tapeShift (T.state y k).cnt y) =
      if T.sel y (k + 1) = a then F (k + 1) y else 1)
    (hone : ∀ k c t, ∫⁻ s, ENNReal.ofReal (G k c (t, s))
      ∂(P.map fun ω => tapeShift c (tapeOf Y ω)) ≤ 1) :
    Supermartingale
      (fun j ω => localWealth (fun i => F i (tapeOf Y ω)) (T.sel (tapeOf Y ω)) a j)
      (T.obsFiltration hm hYm) P := by
  classical
  set W : ℕ → (X → ℕ → ℝ) → ℝ := fun j y => localWealth (fun i => F i y) (T.sel y) a j
    with hW
  have hW0 : ∀ j y, 0 ≤ W j y := fun j y => localWealth_nonneg (fun i => hF0 i y) j
  have htp : Measurable (tapeOf Y) := measurable_tapeOf hYm
  -- the one-step inequality
  have hstep : ∀ (i : ℕ) (g : (X → ℕ → ℝ) → ℝ≥0∞), Measurable g →
      (∀ y, g (T.stopTape i y) = g y) →
      ∫⁻ ω, g (tapeOf Y ω) * ENNReal.ofReal (W (i + 1) (tapeOf Y ω)) ∂P ≤
        ∫⁻ ω, g (tapeOf Y ω) * ENNReal.ofReal (W i (tapeOf Y ω)) ∂P := by
    intro i g hg hgloc
    have h := lintegral_adaptive_segment_le P hYm hind (N := fun y => (T.state y i).cnt)
      (T.measurableSet_cnt hm i) (fun y c => T.cnt_tapeTrunc_iff i y c)
      (g := fun y => g y * ENNReal.ofReal (W i y))
      (hg.mul (ENNReal.measurable_ofReal.comp (hWm i)))
      (fun y => by
        show g (T.stopTape i y) * ENNReal.ofReal (W i (T.stopTape i y)) = _
        rw [hgloc, show W i (T.stopTape i y) = W i y from hWloc i y])
      (Φ := fun c p => ENNReal.ofReal (G i c p))
      (fun c => ENNReal.measurable_ofReal.comp (hGm i c))
      (fun c t => hone i c t)
    refine le_trans (le_of_eq ?_) h
    refine lintegral_congr fun ω => ?_
    show g (tapeOf Y ω) * ENNReal.ofReal (W (i + 1) (tapeOf Y ω)) =
      g (tapeOf Y ω) * ENNReal.ofReal (W i (tapeOf Y ω)) *
        ENNReal.ofReal (G i (T.state (tapeOf Y ω) i).cnt
          (tapeTrunc (T.state (tapeOf Y ω) i).cnt (tapeOf Y ω),
            tapeShift (T.state (tapeOf Y ω) i).cnt (tapeOf Y ω)))
    rw [hGeq i (tapeOf Y ω), mul_assoc, ← ENNReal.ofReal_mul (hW0 i _)]
    congr 2
    exact localWealth_succ _ _ _ _
  have hWle : ∀ j, ∫⁻ ω, ENNReal.ofReal (W j (tapeOf Y ω)) ∂P ≤ 1 := by
    intro j
    induction j with
    | zero => simp [hW]
    | succ j ih =>
      have := hstep j (fun _ => 1) measurable_const (fun _ => rfl)
      simp only [one_mul] at this
      exact this.trans ih
  have hWint : ∀ j, Integrable (fun ω => W j (tapeOf Y ω)) P := fun j =>
    integrable_of_lintegral_ofReal_le_one ((hWm j).comp htp).aestronglyMeasurable
      (fun ω => hW0 j _) (hWle j)
  have hadp : StronglyAdapted (T.obsFiltration hm hYm) (fun j ω => W j (tapeOf Y ω)) := by
    intro j
    have e : (fun ω => W j (tapeOf Y ω)) = (W j) ∘ (fun ω => T.stopTape j (tapeOf Y ω)) := by
      funext ω
      exact (hWloc j _).symm
    show StronglyMeasurable[MeasurableSpace.comap (fun ω => T.stopTape j (tapeOf Y ω))
      inferInstance] (fun ω => W j (tapeOf Y ω))
    rw [e]
    exact ((hWm j).comp (comap_measurable _)).stronglyMeasurable
  refine supermartingale_of_setIntegral_succ_le hadp hWint (fun i s hs => ?_)
  have hs' : MeasurableSet[MeasurableSpace.comap (fun ω => T.stopTape i (tapeOf Y ω))
      inferInstance] s := hs
  obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs'
  have hs0 : MeasurableSet ((fun ω => T.stopTape i (tapeOf Y ω)) ⁻¹' B) :=
    ((T.measurable_stopTape hm i).comp htp) hB
  set g : (X → ℕ → ℝ) → ℝ≥0∞ := fun y => B.indicator 1 (T.stopTape i y) with hg
  have hgm : Measurable g := (measurable_one.indicator hB).comp (T.measurable_stopTape hm i)
  have hgloc : ∀ y, g (T.stopTape i y) = g y := fun y => by
    simp only [hg, T.stopTape_stopTape]
  have hgin : ∀ y, T.stopTape i y ∈ B → g y = 1 := fun y hy =>
    Set.indicator_of_mem hy (1 : (X → ℕ → ℝ) → ℝ≥0∞)
  have hgout : ∀ y, T.stopTape i y ∉ B → g y = 0 := fun y hy =>
    Set.indicator_of_notMem hy (1 : (X → ℕ → ℝ) → ℝ≥0∞)
  have hg1 : ∀ y, g y ≤ 1 := fun y => by
    by_cases hy : T.stopTape i y ∈ B
    · rw [hgin y hy]
    · rw [hgout y hy]
      exact zero_le_one
  have key := hstep i g hgm hgloc
  have conv : ∀ j, ∫ ω in (fun ω => T.stopTape i (tapeOf Y ω)) ⁻¹' B, W j (tapeOf Y ω) ∂P =
      (∫⁻ ω, g (tapeOf Y ω) * ENNReal.ofReal (W j (tapeOf Y ω)) ∂P).toReal := by
    intro j
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => hW0 j _)
      ((hWm j).comp htp).aestronglyMeasurable]
    congr 1
    rw [← lintegral_indicator hs0]
    refine lintegral_congr fun ω => ?_
    by_cases hω : T.stopTape i (tapeOf Y ω) ∈ B
    · have hω' : ω ∈ (fun ω => T.stopTape i (tapeOf Y ω)) ⁻¹' B := hω
      rw [Set.indicator_of_mem hω', hgin _ hω, one_mul]
    · have hω' : ω ∉ (fun ω => T.stopTape i (tapeOf Y ω)) ⁻¹' B := hω
      rw [Set.indicator_of_notMem hω', hgout _ hω, zero_mul]
  show ∫ ω in (fun ω => T.stopTape i (tapeOf Y ω)) ⁻¹' B, W (i + 1) (tapeOf Y ω) ∂P ≤
    ∫ ω in (fun ω => T.stopTape i (tapeOf Y ω)) ⁻¹' B, W i (tapeOf Y ω) ∂P
  rw [conv, conv]
  refine ENNReal.toReal_mono ?_ key
  refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun ω => ?_)
    ((hWle i).trans_lt ENNReal.one_lt_top))
  calc g (tapeOf Y ω) * ENNReal.ofReal (W i (tapeOf Y ω))
      ≤ 1 * ENNReal.ofReal (W i (tapeOf Y ω)) := by gcongr; exact hg1 _
    _ = ENNReal.ofReal (W i (tapeOf Y ω)) := one_mul _

/-- **The likelihood-ratio wealth of the tracker is a nonnegative supermartingale started at
one.**  Model: jointly independent observations `Y x n ~ N(meanₓ, vₓ)`, `vₓ > 0`, on intrinsic
tapes; batch `i + 1` of the tracker is the segment of each tape starting at the (data-dependent)
count after batch `i`, of (data-dependent) length.  The filtration is generated by the consumed
observations (`obsFiltration`).  The wealth is `∏ ½ (1 + q_i(Y_i) / p_i(Y_i))` over the batches
at which `a` is selected, `q_i` the plug-in predictor density and `p_i` the true batch density.
The only hypothesis on the tracker is measurability of the allocation oracles. -/
theorem idealWealth_supermartingale (hm : T.Meas) (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) {mean v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (mean x) (v x).toNNReal) P) (a : A) :
    Supermartingale (fun j ω => T.idealWealth (tapeOf Y ω) mean v a j)
      (T.obsFiltration hm hYm) P :=
  T.factorWealth_supermartingale hm P hYm hind a (fun i y => T.idealF y mean v i)
    (fun k c => T.frozenF mean v k a c) (fun i y => T.idealF_nonneg y mean v i)
    (fun j => T.measurable_idealWealth hm mean v a j)
    (fun j y => T.idealWealth_stopTape y mean v a j)
    (fun k c => T.measurable_frozenF hm mean v k a c)
    (fun k y => T.frozenF_eq mean v k a y)
    (fun k c t => T.lintegral_frozenF_le_one P hYm hind hv hlaw k a c t)

/-- **Coverage of the tracker, measurable tapes.**  See `Tracker.coverage`. -/
theorem coverage_of_measurable (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ j, (∃ z ∈ T.J (T.sel (tapeOf Y ω) j), θ ∈ T.H (T.sel (tapeOf Y ω) j) z) ∧
        T.test (tapeOf Y ω) δ j} ≤ ENNReal.ofReal δ := by
  classical
  set V : A → Set Ω := fun a => {ω | ∃ j, (Fintype.card A : ℝ) / δ ≤
    T.idealWealth (tapeOf Y ω) (fun x => T.pred x θ) v a j} with hVdef
  have hV : ∀ a, P (V a) ≤ ENNReal.ofReal (δ / Fintype.card A) := by
    intro a
    have hK : (0 : ℝ) < Fintype.card A := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
    have hsm := T.idealWealth_supermartingale hm P hYm hind hv hlaw a
    have hvl := ville_ineq hsm (fun j ω => T.idealWealth_nonneg _ _ _ _ _)
      (c := (Fintype.card A : ℝ) / δ) (by positivity)
    refine hvl.trans (le_of_eq ?_)
    congr 1
    simp only [idealWealth, localWealth_zero, integral_const, probReal_univ, smul_eq_mul,
      mul_one]
    rw [one_div_div]
  set Nd : Set Ω := {ω | ∃ x n, Y x n ω = Y x (n + 1) ω} with hNddef
  have hNd : P Nd = 0 := measure_adjacent_eq_zero P hYm hind hv hlaw
  have hincl : {ω | ∃ j, (∃ z ∈ T.J (T.sel (tapeOf Y ω) j),
        θ ∈ T.H (T.sel (tapeOf Y ω) j) z) ∧ T.test (tapeOf Y ω) δ j} ⊆ Nd ∪ ⋃ a, V a := by
    rintro ω ⟨j, ⟨z, hz, hθ⟩, htest⟩
    by_cases hω : ω ∈ Nd
    · exact Or.inl hω
    · refine Or.inr (Set.mem_iUnion.mpr ⟨T.sel (tapeOf Y ω) j, j, ?_⟩)
      have hnd : ∀ i, 1 ≤ i → ∀ x,
          0 < batchVar (T.rr (tapeOf Y ω) i) (T.yb (tapeOf Y ω) i) x := by
        intro i hi x
        refine batchVar_pos_of_ne ((two_le_baseB i).trans (T.baseB_le_rr _ hc hi x)) ?_
        intro heq
        have h' : Y x (T.cntB (tapeOf Y ω) i x + 0) ω = Y x (T.cntB (tapeOf Y ω) i x + 1) ω :=
          heq
        rw [Nat.add_zero] at h'
        exact hω ⟨x, T.cntB (tapeOf Y ω) i x, h'⟩
      exact (htest z hz).trans (T.wealth_le_idealWealth hc _ hv hz hθ hnd j)
  have hsum : ∑ a : A, P (V a) ≤ ENNReal.ofReal δ := by
    rcases isEmpty_or_nonempty A with hA | hA
    · simp
    · have hK : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
      refine (Finset.sum_le_sum fun a _ => hV a).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
  calc P {ω | ∃ j, (∃ z ∈ T.J (T.sel (tapeOf Y ω) j),
        θ ∈ T.H (T.sel (tapeOf Y ω) j) z) ∧ T.test (tapeOf Y ω) δ j}
      ≤ P (Nd ∪ ⋃ a, V a) := measure_mono hincl
    _ ≤ P Nd + ∑ a, P (V a) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_fintype_le _ _))
    _ ≤ ENNReal.ofReal δ := by rw [hNd, zero_add]; exact hsum

/-- **`(ε, δ)`-correctness of the tracker on intrinsic tapes (Theorem `thm:v34-adaptive`, first
claim; Theorem `thm:v34-action-local` for the tracker's batch model).**

Model.  `Y x n` is the `n`-th observation of query type `x`; the observations are jointly
independent with `Y x n ~ N(pred x θ, vₓ)`, `vₓ > 0`.  The tracker `T` satisfies the oracle
contracts (`Tracker.Contract`; only `alloc_base`, the design feasibility and the two outward
enclosures `qlo ≤ q`, `Uhi ≥ U` are used) and its allocation oracles are measurable
(`Tracker.Meas`).  An action `a` is incorrect at `θ` when `θ` lies in one of its closed
invalidating nulls `H a z`, `z ∈ J a`.

Conclusion: the probability that at some batch the stopping test of the `δ`-procedure passes
while the selected action is incorrect is at most `δ`.  In particular the action returned at
the first batch passing the test is incorrect with probability at most `δ`. -/
theorem coverage (hc : T.Contract) (hm : T.Meas) (P : Measure Ω) [IsProbabilityMeasure P]
    {Y : X → ℕ → Ω → ℝ} (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U)
    {v : X → ℝ} (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | ∃ j, (∃ z ∈ T.J (T.sel (fun x n => Y x n ω) j),
        θ ∈ T.H (T.sel (fun x n => Y x n ω) j) z) ∧ T.test (fun x n => Y x n ω) δ j} ≤
      ENNReal.ofReal δ := by
  set Y' : X → ℕ → Ω → ℝ := fun x n => (hlaw x n).aemeasurable.mk (Y x n) with hY'
  have hY'm : ∀ x n, Measurable (Y' x n) := fun x n => (hlaw x n).aemeasurable.measurable_mk
  have hae : ∀ x n, Y x n =ᵐ[P] Y' x n := fun x n => (hlaw x n).aemeasurable.ae_eq_mk
  have hind' : iIndepFun (fun (p : X × ℕ) => Y' p.1 p.2) P :=
    (iIndepFun_congr (fun p : X × ℕ => hae p.1 p.2)).mp hind
  have hlaw' : ∀ x n, HasLaw (Y' x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P :=
    fun x n => (hlaw x n).congr (hae x n).symm
  have hall : ∀ᵐ ω ∂P, ∀ x n, Y x n ω = Y' x n ω := by
    rw [ae_all_iff]
    intro x
    rw [ae_all_iff]
    intro n
    exact hae x n
  have h0 : P {ω | ¬ ∀ x n, Y x n ω = Y' x n ω} = 0 := ae_iff.mp hall
  have hmain := T.coverage_of_measurable hc hm P hY'm hind' θ hv hlaw' hδ
  have hincl : {ω | ∃ j, (∃ z ∈ T.J (T.sel (fun x n => Y x n ω) j),
        θ ∈ T.H (T.sel (fun x n => Y x n ω) j) z) ∧ T.test (fun x n => Y x n ω) δ j} ⊆
      {ω | ∃ j, (∃ z ∈ T.J (T.sel (tapeOf Y' ω) j), θ ∈ T.H (T.sel (tapeOf Y' ω) j) z) ∧
        T.test (tapeOf Y' ω) δ j} ∪ {ω | ¬ ∀ x n, Y x n ω = Y' x n ω} := by
    intro ω hω
    by_cases hω2 : ∀ x n, Y x n ω = Y' x n ω
    · have e : (fun x n => Y x n ω) = tapeOf Y' ω := funext fun x => funext fun n => hω2 x n
      refine Or.inl ?_
      have hω' : ∃ j, (∃ z ∈ T.J (T.sel (fun x n => Y x n ω) j),
          θ ∈ T.H (T.sel (fun x n => Y x n ω) j) z) ∧ T.test (fun x n => Y x n ω) δ j := hω
      rw [e] at hω'
      exact hω'
    · exact Or.inr hω2
  calc P _ ≤ P (_ ∪ _) := measure_mono hincl
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal δ := by rw [h0, add_zero]; exact hmain

end Coverage

end Tracker

/-! ### The tracker's own wealth is a supermartingale when the certified bounds are adapted -/

namespace Tracker

section OwnWealth

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Fintype A]
  [DecidableEq A] (T : Tracker X A Z U)

/-- The certified bounds of the pair `(a, z)` are adapted: they are Borel functions of the
estimates and of the batch, and they only read the batch (the first `r x` entries of each
type).  `Tracker.Contract` does not impose this; it is what makes the tracker's own wealth a
process adapted to the consumed observations. -/
structure BoundsAdapted (T : Tracker X A Z U) (a : A) (z : Z) : Prop where
  qlo_meas : ∀ (j : ℕ) (r : X → ℕ),
    Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) => T.qlo j r p.1 p.2.1 p.2.2
  Uhi_meas : ∀ (j : ℕ) (r : X → ℕ),
    Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) => T.Uhi a z j r p.1 p.2.1 p.2.2
  qlo_local : ∀ (j : ℕ) (r : X → ℕ) (mh vh : X → ℝ) (y y' : X → ℕ → ℝ),
    (∀ x ℓ, ℓ < r x → y x ℓ = y' x ℓ) → T.qlo j r mh vh y = T.qlo j r mh vh y'
  Uhi_local : ∀ (j : ℕ) (r : X → ℕ) (mh vh : X → ℝ) (y y' : X → ℕ → ℝ),
    (∀ x ℓ, ℓ < r x → y x ℓ = y' x ℓ) → T.Uhi a z j r mh vh y = T.Uhi a z j r mh vh y'

omit [Fintype X] [Fintype A] [DecidableEq A] in
lemma batch_congr {y y' : X → ℕ → ℝ} (k : ℕ)
    (hst : ∀ m, m ≤ k + 1 → T.state y' m = T.state y m)
    (hag : ∀ x n, n < (T.state y (k + 1)).cnt x → y' x n = y x n) :
    T.rr y' (k + 1) = T.rr y (k + 1) ∧ T.muh y' (k + 1) = T.muh y (k + 1) ∧
      T.vhh y' (k + 1) = T.vhh y (k + 1) ∧
      ∀ x ℓ, ℓ < T.rr y (k + 1) x → T.yb y' (k + 1) x ℓ = T.yb y (k + 1) x ℓ := by
  have hrr : T.rr y' (k + 1) = T.rr y (k + 1) := by
    unfold rr wnom
    rw [hst (k + 1) le_rfl]
  have hcB : T.cntB y' (k + 1) = T.cntB y (k + 1) := by
    unfold cntB
    rw [hst _ (by omega)]
  have hcB2 : ∀ x, T.cntB y (k + 1) x ≤ (T.state y (k + 1)).cnt x :=
    fun x => T.cnt_mono y (by omega) x
  refine ⟨hrr, ?_, ?_, ?_⟩
  · unfold muh
    rw [hcB]
    exact funext fun x => predMean_congr fun i hi => hag x i (lt_of_lt_of_le hi (hcB2 x))
  · unfold vhh
    rw [hcB]
    exact funext fun x => predVar_congr (k + 1) fun i hi =>
      hag x i (lt_of_lt_of_le hi (hcB2 x))
  · intro x ℓ hℓ
    unfold yb
    rw [hcB]
    refine hag x _ ?_
    have h1 := T.cnt_succ y k x
    have e : T.cntB y (k + 1) x = (T.state y k).cnt x := rfl
    omega

omit [Fintype X] [Fintype A] in
lemma wealth_stopTape {a : A} {z : Z} (hb : T.BoundsAdapted a z) (j : ℕ) (y : X → ℕ → ℝ) :
    T.wealth (T.stopTape j y) a z j = T.wealth y a z j := by
  have hst : ∀ m, m ≤ j → T.state (T.stopTape j y) m = T.state y m :=
    fun m hm => T.state_tapeTrunc j y m (by omega)
  have hag : ∀ x n, n < (T.state y j).cnt x → T.stopTape j y x n = y x n :=
    fun _ _ hn => tapeTrunc_of_lt hn
  unfold wealth localWealth
  refine Finset.prod_congr rfl fun l hl => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hl
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have hsel : T.sel (T.stopTape j y) (k + 1) = T.sel y (k + 1) := by
    unfold sel
    rw [hst _ h2]
  obtain ⟨hrr, hmu, hvh, hyb⟩ := T.batch_congr (y := y) (y' := T.stopTape j y) k
    (fun m hm => hst m (by omega))
    (fun x n hn => hag x n (lt_of_lt_of_le hn (T.cnt_mono y h2 x)))
  have hq : T.qloV (T.stopTape j y) (k + 1) = T.qloV y (k + 1) := by
    unfold qloV
    rw [hrr, hmu, hvh]
    exact hb.qlo_local _ _ _ _ _ _ hyb
  have hU : T.UhiV (T.stopTape j y) a z (k + 1) = T.UhiV y a z (k + 1) := by
    unfold UhiV
    rw [hrr, hmu, hvh]
    exact hb.Uhi_local _ _ _ _ _ _ hyb
  show (if T.sel (T.stopTape j y) (k + 1) = a then
      halfCash (T.qloV (T.stopTape j y) (k + 1)) (T.UhiV (T.stopTape j y) a z (k + 1)) else 1) =
    (if T.sel y (k + 1) = a then halfCash (T.qloV y (k + 1)) (T.UhiV y a z (k + 1)) else 1)
  rw [hsel, hq, hU]

lemma measurable_wealth (hm : T.Meas) {a : A} {z : Z} (hb : T.BoundsAdapted a z) (j : ℕ) :
    Measurable fun y : X → ℕ → ℝ => T.wealth y a z j := by
  unfold wealth localWealth
  refine Finset.measurable_prod _ fun l hl => ?_
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by have := (Finset.mem_Icc.mp hl).1; omega⟩
  refine Measurable.ite (T.measurableSet_sel hm (k + 1) a) ?_ measurable_const
  refine measurable_comp_countable
    (measurableSet_pair_fiber (T.measurableSet_cnt hm k) (T.measurableSet_rr hm (k + 1)))
    (Ψ := fun d y => halfCash
      (T.qlo (k + 1) d.2 (fun x => predMean (y x) (d.1 x))
        (fun x => predVar (k + 1) (y x) (d.1 x)) (tapeShift d.1 y))
      (T.Uhi a z (k + 1) d.2 (fun x => predMean (y x) (d.1 x))
        (fun x => predVar (k + 1) (y x) (d.1 x)) (tapeShift d.1 y)))
    (fun d => ?_) (fun y => rfl)
  have harg : Measurable fun y : X → ℕ → ℝ =>
      (((fun x => predMean (y x) (d.1 x)), (fun x => predVar (k + 1) (y x) (d.1 x)),
        tapeShift d.1 y) : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ)) :=
    (measurable_pi_iff.mpr fun x => measurable_predMean x (d.1 x)).prodMk
      ((measurable_pi_iff.mpr fun x => measurable_predVar (k + 1) x (d.1 x)).prodMk
        (measurable_tapeShift d.1))
  have hq := (hb.qlo_meas (k + 1) d.2).comp harg
  have hU := (hb.Uhi_meas (k + 1) d.2).comp harg
  exact measurable_halfCash (by simpa only [Function.comp_def] using hq)
    (by simpa only [Function.comp_def] using hU)

/-- The tracker's factor of batch `k + 1` for the pair `(a, z)` as a function of the consumed
block (counts frozen at `c`) and of the next segment. -/
def realG (a : A) (z : Z) (k : ℕ) (c : X → ℕ) (p : (X → ℕ → ℝ) × (X → ℕ → ℝ)) : ℝ :=
  if T.sel p.1 (k + 1) = a then
    halfCash (T.qlo (k + 1) (T.rr p.1 (k + 1)) (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2)
      (T.Uhi a z (k + 1) (T.rr p.1 (k + 1)) (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2)
  else 1

lemma measurable_realG (hm : T.Meas) {a : A} {z : Z} (hb : T.BoundsAdapted a z) (k : ℕ)
    (c : X → ℕ) : Measurable (T.realG a z k c) := by
  have hbody : Measurable fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) =>
      halfCash (T.qlo (k + 1) (T.rr p.1 (k + 1)) (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2)
      (T.Uhi a z (k + 1) (T.rr p.1 (k + 1)) (fun x => predMean (p.1 x) (c x))
        (fun x => predVar (k + 1) (p.1 x) (c x)) p.2) := by
    refine measurable_comp_countable (D := fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) => T.rr p.1 (k + 1))
      (fun r => measurable_fst (T.measurableSet_rr hm (k + 1) r))
      (Ψ := fun r p => halfCash (T.qlo (k + 1) r (fun x => predMean (p.1 x) (c x))
          (fun x => predVar (k + 1) (p.1 x) (c x)) p.2)
        (T.Uhi a z (k + 1) r (fun x => predMean (p.1 x) (c x))
          (fun x => predVar (k + 1) (p.1 x) (c x)) p.2))
      (fun r => ?_) (fun p => rfl)
    have harg : Measurable fun p : (X → ℕ → ℝ) × (X → ℕ → ℝ) =>
        (((fun x => predMean (p.1 x) (c x)), (fun x => predVar (k + 1) (p.1 x) (c x)),
          p.2) : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ)) :=
      ((measurable_pi_iff.mpr fun x => measurable_predMean x (c x)).comp
          (measurable_fst : Measurable (Prod.fst : (X → ℕ → ℝ) × (X → ℕ → ℝ) → X → ℕ → ℝ))).prodMk
        (((measurable_pi_iff.mpr fun x => measurable_predVar (k + 1) x (c x)).comp
          (measurable_fst : Measurable (Prod.fst : (X → ℕ → ℝ) × (X → ℕ → ℝ) → X → ℕ → ℝ))).prodMk
            measurable_snd)
    have hq := (hb.qlo_meas (k + 1) r).comp harg
    have hU := (hb.Uhi_meas (k + 1) r).comp harg
    exact measurable_halfCash (by simpa only [Function.comp_def] using hq)
      (by simpa only [Function.comp_def] using hU)
  exact Measurable.ite (measurable_fst (T.measurableSet_sel hm (k + 1) a)) hbody measurable_const

omit [Fintype X] [Fintype A] in
lemma realG_eq (a : A) (z : Z) (k : ℕ) (y : X → ℕ → ℝ) :
    T.realG a z k (T.state y k).cnt
        (tapeTrunc (T.state y k).cnt y, tapeShift (T.state y k).cnt y) =
      if T.sel y (k + 1) = a then halfCash (T.qloV y (k + 1)) (T.UhiV y a z (k + 1)) else 1 := by
  have hst := T.state_tapeTrunc k y
  have hsel : T.sel (tapeTrunc (T.state y k).cnt y) (k + 1) = T.sel y (k + 1) := by
    unfold sel
    rw [hst _ le_rfl]
  have hrr : T.rr (tapeTrunc (T.state y k).cnt y) (k + 1) = T.rr y (k + 1) := by
    unfold rr wnom
    rw [hst _ le_rfl]
  have hpm : (fun x => predMean (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x)) =
      T.muh y (k + 1) :=
    funext fun x => predMean_congr fun i hi => tapeTrunc_of_lt hi
  have hpv : (fun x => predVar (k + 1) (tapeTrunc (T.state y k).cnt y x)
      ((T.state y k).cnt x)) = T.vhh y (k + 1) :=
    funext fun x => predVar_congr (k + 1) fun i hi => tapeTrunc_of_lt hi
  show (if T.sel (tapeTrunc (T.state y k).cnt y) (k + 1) = a then
      halfCash (T.qlo (k + 1) (T.rr (tapeTrunc (T.state y k).cnt y) (k + 1))
        (fun x => predMean (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x))
        (fun x => predVar (k + 1) (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x))
        (tapeShift (T.state y k).cnt y))
      (T.Uhi a z (k + 1) (T.rr (tapeTrunc (T.state y k).cnt y) (k + 1))
        (fun x => predMean (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x))
        (fun x => predVar (k + 1) (tapeTrunc (T.state y k).cnt y x) ((T.state y k).cnt x))
        (tapeShift (T.state y k).cnt y)) else 1) = _
  rw [hsel, hrr, hpm, hpv]
  rfl

/-- **Action-local wealth of the tracker is a nonnegative supermartingale started at one
(Theorem `thm:v34-action-local`, first claim, for the tracker on intrinsic tapes).**

Model: jointly independent observations `Y x n ~ N(pred x θ, vₓ)`, `vₓ > 0`; the tracker
satisfies the oracle contracts and its allocation oracles are measurable; `θ` lies in the
component null `H a z`, `z ∈ J a`; and the certified bounds of `(a, z)` are adapted
(`BoundsAdapted`: Borel, and reading only the batch).  Then
`j ↦ E^loc_{a,z}(j) = T.wealth · a z j` is a supermartingale for the filtration of consumed
observations.  Nonnegativity is `localWealth_nonneg` and the initial value `localWealth_zero`.

Without `BoundsAdapted` the wealth need not be measurable; the coverage theorem
`Tracker.coverage` does not need it, because the wealth is dominated by the supermartingale of
`idealWealth_supermartingale` (`wealth_le_idealWealth`). -/
theorem wealth_supermartingale (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] {Y : X → ℕ → Ω → ℝ} (hYm : ∀ x n, Measurable (Y x n))
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P) (θ : U) {v : X → ℝ}
    (hv : ∀ x, 0 < v x)
    (hlaw : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P)
    {a : A} {z : Z} (hz : z ∈ T.J a) (hθ : θ ∈ T.H a z) (hb : T.BoundsAdapted a z) :
    Supermartingale (fun j ω => T.wealth (tapeOf Y ω) a z j) (T.obsFiltration hm hYm) P := by
  refine T.factorWealth_supermartingale hm P hYm hind a
    (fun i y => halfCash (T.qloV y i) (T.UhiV y a z i)) (fun k c => T.realG a z k c)
    (fun i y => ?_) (fun j => T.measurable_wealth hm hb j)
    (fun j y => T.wealth_stopTape hb j y) (fun k c => T.measurable_realG hm hb k c)
    (fun k y => T.realG_eq a z k y) (fun k c t => ?_)
  · have := halfCash_ge_half
      (hc.qlo_nonneg i (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i))
      (hc.Uhi_nonneg a z i (T.rr y i) (T.muh y i) (T.vhh y i) (T.yb y i))
    unfold qloV UhiV
    linarith
  · have hS : Measurable (fun ω => tapeShift c (tapeOf Y ω)) :=
      (measurable_tapeShift c).comp (measurable_tapeOf hYm)
    have : IsProbabilityMeasure (P.map fun ω => tapeShift c (tapeOf Y ω)) :=
      (Measure.isProbabilityMeasure_map_iff hS.aemeasurable).mpr inferInstance
    have hdefG : ∀ s, T.realG a z k c (t, s) =
        if T.sel t (k + 1) = a then
          halfCash (T.qlo (k + 1) (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
              (fun x => predVar (k + 1) (t x) (c x)) s)
            (T.Uhi a z (k + 1) (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
              (fun x => predVar (k + 1) (t x) (c x)) s)
        else 1 := fun s => rfl
    have hdefF : ∀ s, T.frozenF (fun x => T.pred x θ) v k a c (t, s) =
        if T.sel t (k + 1) = a then
          halfCash (batchDens (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
              (fun x => predVar (k + 1) (t x) (c x)) s)
            (batchDens (T.rr t (k + 1)) (fun x => T.pred x θ) v s)
        else 1 := fun s => rfl
    by_cases h : T.sel t (k + 1) = a
    · have hae : ∀ᵐ ω ∂P, ¬ ∃ x n, Y x n ω = Y x (n + 1) ω := by
        have h0 := measure_adjacent_eq_zero P hYm hind hv hlaw
        rw [ae_iff]
        simpa only [not_not] using h0
      have hmG : Measurable fun s : X → ℕ → ℝ => ENNReal.ofReal (T.realG a z k c (t, s)) :=
        (ENNReal.measurable_ofReal.comp (T.measurable_realG hm hb k c)).comp
          measurable_prodMk_left
      have hmF : Measurable fun s : X → ℕ → ℝ =>
          ENNReal.ofReal (T.frozenF (fun x => T.pred x θ) v k a c (t, s)) :=
        (ENNReal.measurable_ofReal.comp
          (T.measurable_frozenF hm (fun x => T.pred x θ) v k a c)).comp measurable_prodMk_left
      calc ∫⁻ s, ENNReal.ofReal (T.realG a z k c (t, s))
            ∂(P.map fun ω => tapeShift c (tapeOf Y ω))
          = ∫⁻ ω, ENNReal.ofReal (T.realG a z k c (t, tapeShift c (tapeOf Y ω))) ∂P :=
            lintegral_map hmG hS
        _ ≤ ∫⁻ ω, ENNReal.ofReal
              (T.frozenF (fun x => T.pred x θ) v k a c (t, tapeShift c (tapeOf Y ω))) ∂P := by
            refine lintegral_mono_ae (hae.mono fun ω hω => ?_)
            apply ENNReal.ofReal_le_ofReal
            rw [hdefG, hdefF, ite_eq_left h, ite_eq_left h]
            have hk1 : 1 ≤ k + 1 := by omega
            have hvh : ∀ x, 0 < predVar (k + 1) (t x) (c x) := fun x => predVar_pos hk1 _ _
            have hnd : ∀ x, 0 < batchVar (T.rr t (k + 1)) (tapeShift c (tapeOf Y ω)) x := by
              intro x
              refine batchVar_pos_of_ne ((two_le_baseB (k + 1)).trans
                (T.baseB_le_rr t hc hk1 x)) ?_
              intro heq
              have h' : Y x (c x + 0) ω = Y x (c x + 1) ω := heq
              rw [Nat.add_zero] at h'
              exact hω ⟨x, c x, h'⟩
            have hp : 0 < batchDens (T.rr t (k + 1)) (fun x => T.pred x θ) v
                (tapeShift c (tapeOf Y ω)) := batchDens_pos _ _ hv _
            have hU := (batchDens_le_nullEnv hnd hθ hv).trans
              (hc.Uhi_ge a z (k + 1) (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
                (fun x => predVar (k + 1) (t x) (c x)) _ hz hnd)
            have hq := hc.qlo_le (k + 1) (T.rr t (k + 1)) (fun x => predMean (t x) (c x))
              (fun x => predVar (k + 1) (t x) (c x)) (tapeShift c (tapeOf Y ω)) hvh
            have hle := div_le_div₀ (batchDens_nonneg _ _ _ _) hq hp hU
            unfold halfCash
            linarith
        _ = ∫⁻ s, ENNReal.ofReal (T.frozenF (fun x => T.pred x θ) v k a c (t, s))
              ∂(P.map fun ω => tapeShift c (tapeOf Y ω)) := (lintegral_map hmF hS).symm
        _ ≤ 1 := T.lintegral_frozenF_le_one P hYm hind hv hlaw k a c t
    · have hΦ : ∀ s, T.realG a z k c (t, s) = 1 := fun s => by rw [hdefG s, ite_eq_right h]
      simp [hΦ]

end OwnWealth

end Tracker

/-! ### The oracle contracts are satisfiable -/

section Instance

variable {X : Type*} [Fintype X]

/-- Estimates with positive variance coordinates. -/
def posSet (X : Type*) : Set ((X → ℝ) × (X → ℝ)) := {q | ∀ x, 0 < q.2 x}

omit [Fintype X] in
lemma measurableSet_posSet [Countable X] : MeasurableSet (posSet X) := by
  have : posSet X = ⋂ x, {q : (X → ℝ) × (X → ℝ) | 0 < q.2 x} := by
    ext q
    constructor
    · intro h
      exact Set.mem_iInter.mpr fun x => h x
    · intro h
      exact fun x => Set.mem_iInter.mp h x
  rw [this]
  exact MeasurableSet.iInter fun x =>
    measurableSet_lt measurable_const ((measurable_pi_apply x).comp measurable_snd)

/-- A function of the estimates that satisfies the perturbation bound of Lemma
`lem:v34-transport` is continuous on the positive-variance region. -/
lemma continuousOn_of_transport {F : (X → ℝ) × (X → ℝ) → ℝ}
    (hF : ∀ (m v m' v' : X → ℝ) (d : ℝ), (∀ x, 0 < v x) → (∀ x, 0 < v' x) →
      (∀ x, |m x - m' x| / (2 * Real.sqrt (min (v x) (v' x))) +
        1 / 2 * |Real.log (v x / v' x)| ≤ d) → |F (m, v) - F (m', v')| ≤ d) :
    ContinuousOn F (posSet X) := by
  intro q0 hq0
  set term : (X → ℝ) × (X → ℝ) → X → ℝ := fun q x =>
    |q.1 x - q0.1 x| / (2 * Real.sqrt (min (q.2 x) (q0.2 x))) +
      1 / 2 * |Real.log (q.2 x / q0.2 x)| with hterm
  have hterm0 : ∀ q x, 0 ≤ term q x := fun q x => by
    simp only [hterm]
    positivity
  have hq0term : ∀ x, term q0 x = 0 := fun x => by
    have hv0 : q0.2 x ≠ 0 := (hq0 x).ne'
    simp [hterm, div_self hv0]
  have hcont : ∀ x, Tendsto (fun q => term q x) (𝓝 q0) (𝓝 (term q0 x)) := by
    intro x
    have hv0 : 0 < q0.2 x := hq0 x
    have c1 : Continuous fun q : (X → ℝ) × (X → ℝ) => q.1 x :=
      (continuous_apply x).comp continuous_fst
    have c2 : Continuous fun q : (X → ℝ) × (X → ℝ) => q.2 x :=
      (continuous_apply x).comp continuous_snd
    have hnum : ContinuousAt (fun q : (X → ℝ) × (X → ℝ) => |q.1 x - q0.1 x|) q0 :=
      (c1.sub continuous_const).abs.continuousAt
    have hden : ContinuousAt (fun q : (X → ℝ) × (X → ℝ) =>
        2 * Real.sqrt (min (q.2 x) (q0.2 x))) q0 :=
      (continuous_const.mul (Real.continuous_sqrt.comp (c2.min continuous_const))).continuousAt
    have hden0 : 2 * Real.sqrt (min (q0.2 x) (q0.2 x)) ≠ 0 := by
      rw [min_self]
      have := Real.sqrt_pos.mpr hv0
      positivity
    have hlog : ContinuousAt (fun q : (X → ℝ) × (X → ℝ) => Real.log (q.2 x / q0.2 x)) q0 := by
      refine ContinuousAt.log (c2.div_const _).continuousAt ?_
      rw [div_self hv0.ne']
      exact one_ne_zero
    exact (hnum.div hden hden0).add (continuousAt_const.mul hlog.abs)
  have hsum : Tendsto (fun q => ∑ x, term q x) (𝓝 q0) (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset X) fun x _ => hcont x
    rwa [Finset.sum_eq_zero fun x _ => hq0term x] at h
  show ContinuousWithinAt F (posSet X) q0
  rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    (eventually_nhdsWithin_of_forall fun q hq => ?_) (hsum.mono_left nhdsWithin_le_nhds)
  rw [Real.dist_eq]
  exact hF q.1 q.2 q0.1 q0.2 _ hq hq0 fun x =>
    Finset.single_le_sum (f := term q) (fun x _ => hterm0 q x) (Finset.mem_univ x)

open Classical in
/-- Extension by zero outside the positive-variance region. -/
def posExt (F : (X → ℝ) × (X → ℝ) → ℝ) (q : (X → ℝ) × (X → ℝ)) : ℝ :=
  if q ∈ posSet X then F q else 0

lemma measurable_posExt {F : (X → ℝ) × (X → ℝ) → ℝ} (hF : ContinuousOn F (posSet X)) :
    Measurable (posExt F) := by
  classical
  exact hF.measurable_piecewise (g := fun _ => (0 : ℝ)) continuous_const.continuousOn
    measurableSet_posSet

omit [Fintype X] in
lemma posExt_of_mem {F : (X → ℝ) × (X → ℝ) → ℝ} {q : (X → ℝ) × (X → ℝ)} (hq : q ∈ posSet X) :
    posExt F q = F q := by
  unfold posExt
  exact ite_eq_left hq

variable [Nonempty X]

lemma uvc_simplex_nonempty (X : Type*) [Fintype X] [Nonempty X] : Nonempty (simplex X) := by
  classical
  obtain ⟨x0⟩ := ‹Nonempty X›
  exact ⟨⟨_, single_mem_simplex x0⟩⟩

/-- A dense sequence of designs. -/
def canonDense (X : Type*) [Fintype X] [Nonempty X] (n : ℕ) : X → ℝ :=
  haveI := uvc_simplex_nonempty X
  (TopologicalSpace.denseSeq (simplex X) n).1

lemma canonDense_mem (n : ℕ) : canonDense X n ∈ simplex X := by
  unfold canonDense
  exact Subtype.property _

/-- Every design is dominated, up to the factor `1 - t`, by a design of the dense sequence. -/
lemma canonDense_dom {w : X → ℝ} (hw : w ∈ simplex X) {t : ℝ} (ht : 0 < t) :
    ∃ n, ∀ x, (1 - t) * w x ≤ canonDense X n x := by
  have := uvc_simplex_nonempty X
  set O : Set (simplex X) := ⋂ x, {u : simplex X | (1 - t) * w x < u.1 x ∨ w x = 0} with hO
  have hOopen : IsOpen O := by
    refine isOpen_iInter_of_finite fun x => ?_
    by_cases hx : w x = 0
    · have : {u : simplex X | (1 - t) * w x < u.1 x ∨ w x = 0} = Set.univ :=
        Set.eq_univ_of_forall fun u => Or.inr hx
      rw [this]
      exact isOpen_univ
    · have : {u : simplex X | (1 - t) * w x < u.1 x ∨ w x = 0} =
          {u : simplex X | (1 - t) * w x < u.1 x} := by
        ext u
        constructor
        · rintro (h | h)
          · exact h
          · exact absurd h hx
        · intro h
          exact Or.inl h
      rw [this]
      exact isOpen_lt continuous_const ((continuous_apply x).comp continuous_subtype_val)
  have hOne : O.Nonempty := by
    refine ⟨⟨w, hw⟩, Set.mem_iInter.mpr fun x => ?_⟩
    by_cases hx : w x = 0
    · exact Or.inr hx
    · refine Or.inl ?_
      have hpos : 0 < w x := lt_of_le_of_ne (hw.1 x) (Ne.symm hx)
      show (1 - t) * w x < w x
      nlinarith
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (simplex X)).exists_mem_open
    hOopen hOne
  refine ⟨n, fun x => ?_⟩
  have hx := Set.mem_iInter.mp hn x
  have hx' : (1 - t) * w x < (TopologicalSpace.denseSeq (simplex X) n).1 x ∨ w x = 0 := hx
  rcases hx' with h | h
  · exact h.le
  · rw [h, mul_zero]
    exact (canonDense_mem n).1 x

/-- A design of the dense sequence is `e`-optimal for the information game at any estimates
with positive variances. -/
lemma exists_near_opt {Z U : Type*} (J : Finset Z) (hJ : J.Nonempty) (H : Z → Set U)
    (pred : X → U → ℝ) {m v : X → ℝ} (hv : ∀ x, 0 < v x) {e : ℝ} (he : 0 < e) :
    ∃ n, actGameStar J hJ H pred m v ≤ actGame J hJ H pred (canonDense X n) m v + e := by
  have := uvc_simplex_nonempty X
  set S := actGameStar J hJ H pred m v with hS
  have hS0 : 0 ≤ S :=
    (actGame_nonneg (canonDense_mem 0).1 hv).trans
      (actGame_le_star J hJ H pred (canonDense_mem 0) hv)
  have hlt : S - e / 2 < ⨆ w : simplex X, actGame J hJ H pred w m v := by
    show S - e / 2 < actGameStar J hJ H pred m v
    linarith
  obtain ⟨⟨w, hw⟩, hwlt⟩ := exists_lt_of_lt_ciSup hlt
  have hwle : actGame J hJ H pred w m v ≤ S := actGame_le_star J hJ H pred hw hv
  set t := min 1 (e / (2 * (S + 1))) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t * (2 * (S + 1)) ≤ e := by
    have h1 : t ≤ e / (2 * (S + 1)) := min_le_right _ _
    exact (le_div_iff₀ (by positivity)).mp h1
  obtain ⟨n, hn⟩ := canonDense_dom hw ht0
  have hdom := actGame_domination J hJ H pred (μ := m) (c := 1 - t) (by linarith) hw.1 hn hv
  refine ⟨n, ?_⟩
  have h3 : t * actGame J hJ H pred w m v ≤ t * S := mul_le_mul_of_nonneg_left hwle ht0.le
  have h4 : t * S ≤ e / 2 := by nlinarith
  have h5 : (1 - t) * actGame J hJ H pred w m v =
      actGame J hJ H pred w m v - t * actGame J hJ H pred w m v := by ring
  linarith

/-! #### A measurable tie-breaking rule: the maximizer of lowest index -/

section Pick

variable {A : Type*} [Fintype A]

/-- `a` is the maximizer of `f` of lowest index. -/
def IsFirstMax (f : A → ℝ) (a : A) : Prop :=
  (∀ b, f b ≤ f a) ∧ ∀ b, (Fintype.equivFin A b : ℕ) < (Fintype.equivFin A a : ℕ) → f b < f a

lemma exists_isFirstMax [Nonempty A] (f : A → ℝ) : ∃ a, IsFirstMax f a := by
  classical
  obtain ⟨a0, -, ha0⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  set M : Finset A := Finset.univ.filter fun b => f b = f a0 with hM
  have hMne : M.Nonempty := ⟨a0, by simp [hM]⟩
  obtain ⟨a, haM, hmin⟩ := Finset.exists_min_image M (fun b => (Fintype.equivFin A b : ℕ)) hMne
  have hfa : f a = f a0 := (Finset.mem_filter.mp haM).2
  refine ⟨a, fun b => by rw [hfa]; exact ha0 b (Finset.mem_univ b), fun b hb => ?_⟩
  by_contra hcon
  have h1 : f b = f a0 := le_antisymm (ha0 b (Finset.mem_univ b)) (by rw [← hfa]; exact not_lt.mp hcon)
  have h2 : b ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ b, h1⟩
  have h3 := hmin b h2
  omega

lemma isFirstMax_unique {f : A → ℝ} {a a' : A} (h1 : IsFirstMax f a) (h2 : IsFirstMax f a') :
    a = a' := by
  rcases lt_trichotomy (Fintype.equivFin A a : ℕ) (Fintype.equivFin A a' : ℕ) with h | h | h
  · exact absurd (h2.2 a h) (not_lt.mpr (h1.1 a'))
  · exact (Fintype.equivFin A).injective (Fin.ext h)
  · exact absurd (h1.2 a' h) (not_lt.mpr (h2.1 a))

/-- The tie-breaking rule: the displayed maximizer of lowest index. -/
def canonPick [Nonempty A] (f : A → ℝ) : A := Classical.choose (exists_isFirstMax f)

lemma canonPick_spec [Nonempty A] (f : A → ℝ) : IsFirstMax f (canonPick f) :=
  Classical.choose_spec (exists_isFirstMax f)

lemma measurableSet_canonPick [Nonempty A] (a : A) :
    MeasurableSet {f : A → ℝ | canonPick f = a} := by
  have : {f : A → ℝ | canonPick f = a} =
      (⋂ b, {f : A → ℝ | f b ≤ f a}) ∩
        ⋂ b, {f : A → ℝ | (Fintype.equivFin A b : ℕ) < (Fintype.equivFin A a : ℕ) →
          f b < f a} := by
    ext f
    constructor
    · intro h
      have h' : canonPick f = a := h
      have hs := canonPick_spec f
      rw [h'] at hs
      exact ⟨Set.mem_iInter.mpr fun b => hs.1 b, Set.mem_iInter.mpr fun b => hs.2 b⟩
    · rintro ⟨h1, h2⟩
      have hs : IsFirstMax f a :=
        ⟨fun b => Set.mem_iInter.mp h1 b, fun b => Set.mem_iInter.mp h2 b⟩
      exact isFirstMax_unique (canonPick_spec f) hs
  rw [this]
  refine (MeasurableSet.iInter fun b =>
    measurableSet_le (measurable_pi_apply b) (measurable_pi_apply a)).inter
    (MeasurableSet.iInter fun b => ?_)
  by_cases hb : (Fintype.equivFin A b : ℕ) < (Fintype.equivFin A a : ℕ)
  · have : {f : A → ℝ | (Fintype.equivFin A b : ℕ) < (Fintype.equivFin A a : ℕ) → f b < f a} =
        {f : A → ℝ | f b < f a} := by
      ext f
      constructor
      · intro h
        exact h hb
      · intro h _
        exact h
    rw [this]
    exact measurableSet_lt (measurable_pi_apply b) (measurable_pi_apply a)
  · have : {f : A → ℝ | (Fintype.equivFin A b : ℕ) < (Fintype.equivFin A a : ℕ) → f b < f a} =
        Set.univ := Set.eq_univ_of_forall fun f h => absurd h hb
    rw [this]
    exact MeasurableSet.univ

end Pick

/-! #### A measurable rounding rule -/

open Classical in
/-- Rounding with baseline: `b_j + ⌊M_j wₓ⌋`, the remaining units of the clock going to a
fixed type. -/
def canonAlloc (x0 : X) (j : ℕ) (w : X → ℝ) (x : X) : ℕ :=
  baseB j + ⌊(clockM j : ℝ) * w x⌋₊ +
    if x = x0 then clockM j - ∑ x', ⌊(clockM j : ℝ) * w x'⌋₊ else 0

omit [Nonempty X] in
lemma canonAlloc_sum (x0 : X) (j : ℕ) {w : X → ℝ} (hw : w ∈ simplex X) :
    ∑ x, canonAlloc x0 j w x = batchR (Fintype.card X) j := by
  classical
  have hle : ∑ x', ⌊(clockM j : ℝ) * w x'⌋₊ ≤ clockM j := by
    have h1 : (∑ x', (⌊(clockM j : ℝ) * w x'⌋₊ : ℝ)) ≤ ∑ x', (clockM j : ℝ) * w x' :=
      Finset.sum_le_sum fun x' _ =>
        Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hw.1 x'))
    rw [← Finset.mul_sum, hw.2, mul_one] at h1
    exact_mod_cast h1
  unfold canonAlloc
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, Finset.sum_ite_eq' Finset.univ x0, ite_eq_left (Finset.mem_univ x0)]
  unfold batchR
  omega

omit [Nonempty X] in
lemma canonAlloc_dom (x0 : X) (j : ℕ) (w : X → ℝ) (x : X) :
    (clockM j : ℝ) * w x ≤ canonAlloc x0 j w x := by
  have h1 := Nat.lt_floor_add_one ((clockM j : ℝ) * w x)
  have h2 := two_le_baseB j
  have h3 : ⌊(clockM j : ℝ) * w x⌋₊ + 1 ≤ canonAlloc x0 j w x := by
    unfold canonAlloc
    omega
  have h4 : ((⌊(clockM j : ℝ) * w x⌋₊ : ℝ) + 1) ≤ (canonAlloc x0 j w x : ℝ) := by
    exact_mod_cast h3
  linarith

omit [Nonempty X] in
lemma measurable_canonAlloc (x0 : X) (j : ℕ) (x : X) :
    Measurable fun w : X → ℝ => canonAlloc x0 j w x := by
  classical
  have hfl : ∀ x' : X, Measurable fun w : X → ℝ => ⌊(clockM j : ℝ) * w x'⌋₊ := fun x' =>
    Nat.measurable_floor.comp (measurable_const.mul (measurable_pi_apply x'))
  have hsum : Measurable fun w : X → ℝ => ∑ x', ⌊(clockM j : ℝ) * w x'⌋₊ :=
    Finset.measurable_sum _ fun x' _ => hfl x'
  unfold canonAlloc
  by_cases hx : x = x0
  · simp only [hx, ↓reduceIte]
    exact (measurable_const.add (hfl x0)).add (measurable_const.sub hsum)
  · simp only [hx, ↓reduceIte]
    exact (measurable_const.add (hfl x)).add measurable_const

/-! #### A measurable null envelope -/

section Guarded

variable {U : Type*}

omit [Fintype X] [Nonempty X] in
lemma continuous_batchVar (r : X → ℕ) (x : X) :
    Continuous fun y : X → ℕ → ℝ => batchVar r y x := by
  unfold batchVar batchMean
  fun_prop

omit [Nonempty X] in
lemma continuous_batchDens (r : X → ℕ) (t s : X → ℝ) : Continuous (batchDens r t s) := by
  have hpdf : ∀ x, Continuous (gaussianPDFReal (t x) (s x).toNNReal) := by
    intro x
    rw [gaussianPDFReal_def]
    fun_prop
  have hB : ∀ (x : X) (ℓ : ℕ), Continuous fun y : X → ℕ → ℝ =>
      gaussianPDFReal (t x) (s x).toNNReal (y x ℓ) := by
    intro x ℓ
    have h := (hpdf x).comp ((continuous_apply ℓ).comp (continuous_apply x) :
      Continuous fun y : X → ℕ → ℝ => y x ℓ)
    simpa only [Function.comp_def] using h
  unfold batchDens
  exact continuous_finsetProd _ fun x _ => continuous_finsetProd _ fun ℓ _ => hB x ℓ

omit [Fintype X] [Nonempty X] in
lemma batchVar_congr {r : X → ℕ} {y y' : X → ℕ → ℝ} (h : ∀ x ℓ, ℓ < r x → y x ℓ = y' x ℓ)
    (x : X) : batchVar r y x = batchVar r y' x := by
  have hm : batchMean r y x = batchMean r y' x := by
    unfold batchMean
    rw [Finset.sum_congr rfl fun ℓ hℓ => h x ℓ (Finset.mem_range.mp hℓ)]
  unfold batchVar
  rw [hm, Finset.sum_congr rfl fun ℓ hℓ => by rw [h x ℓ (Finset.mem_range.mp hℓ)]]

open Classical in
/-- The null envelope on nondegenerate batches (positive within-batch centered variances),
and `1` on degenerate batches, where the supremum can be infinite. -/
def guardedEnv (H : Set U) (pred : X → U → ℝ) (r : X → ℕ) (y : X → ℕ → ℝ) : ℝ :=
  if ∀ x, 0 < batchVar r y x then nullEnv H pred r y else 1

omit [Nonempty X] in
lemma guardedEnv_of_nondeg {H : Set U} {pred : X → U → ℝ} {r : X → ℕ} {y : X → ℕ → ℝ}
    (h : ∀ x, 0 < batchVar r y x) : guardedEnv H pred r y = nullEnv H pred r y := by
  unfold guardedEnv
  exact ite_eq_left h

omit [Nonempty X] in
lemma guardedEnv_nonneg (H : Set U) (pred : X → U → ℝ) (r : X → ℕ) (y : X → ℕ → ℝ) :
    0 ≤ guardedEnv H pred r y := by
  unfold guardedEnv
  split_ifs
  · exact Real.iSup_nonneg fun p => batchDens_nonneg _ _ _ _
  · exact zero_le_one

omit [Nonempty X] in
lemma guardedEnv_congr (H : Set U) (pred : X → U → ℝ) {r : X → ℕ} {y y' : X → ℕ → ℝ}
    (h : ∀ x ℓ, ℓ < r x → y x ℓ = y' x ℓ) : guardedEnv H pred r y = guardedEnv H pred r y' := by
  have hE : nullEnv H pred r y = nullEnv H pred r y' := by
    unfold nullEnv
    exact iSup_congr fun p => batchDens_congr h
  have hV : (∀ x, 0 < batchVar r y x) ↔ ∀ x, 0 < batchVar r y' x := by
    constructor
    · intro h1 x
      rw [← batchVar_congr h x]
      exact h1 x
    · intro h1 x
      rw [batchVar_congr h x]
      exact h1 x
  unfold guardedEnv
  by_cases hy : ∀ x, 0 < batchVar r y x
  · rw [ite_eq_left hy, ite_eq_left (hV.mp hy), hE]
  · rw [ite_eq_right hy, ite_eq_right (fun h' => hy (hV.mpr h'))]

omit [Nonempty X] in
/-- The guarded envelope is a Borel function of the batch: on the open set of nondegenerate
batches it is a supremum of continuous functions that is bounded above. -/
lemma measurable_guardedEnv (H : Set U) (pred : X → U → ℝ) (r : X → ℕ) :
    Measurable (guardedEnv H pred r) := by
  classical
  set N : Set (X → ℕ → ℝ) := {y | ∀ x, 0 < batchVar r y x} with hN
  have hNo : IsOpen N := by
    have : N = ⋂ x, {y : X → ℕ → ℝ | 0 < batchVar r y x} := by
      ext y
      constructor
      · intro h
        exact Set.mem_iInter.mpr fun x => h x
      · intro h
        exact fun x => Set.mem_iInter.mp h x
    rw [this]
    exact isOpen_iInter_of_finite fun x => isOpen_lt continuous_const (continuous_batchVar r x)
  have hNm : MeasurableSet N := hNo.measurableSet
  have hin : ∀ y, y ∈ N → guardedEnv H pred r y = nullEnv H pred r y :=
    fun y hy => guardedEnv_of_nondeg hy
  have hout : ∀ y, y ∉ N → guardedEnv H pred r y = 1 := fun y hy => by
    unfold guardedEnv
    exact ite_eq_right hy
  refine measurable_of_Ioi fun c => ?_
  rcases isEmpty_or_nonempty {p : U × (X → ℝ) // p.1 ∈ H ∧ ∀ x, 0 < p.2 x} with hI | hI
  · -- the envelope vanishes
    have h0 : ∀ y, nullEnv H pred r y = 0 := fun y => by
      unfold nullEnv
      exact Real.iSup_of_isEmpty _
    have : guardedEnv H pred r ⁻¹' Set.Ioi c = (N ∩ {_y | c < 0}) ∪ (Nᶜ ∩ {_y | c < 1}) := by
      ext y
      by_cases hy : y ∈ N
      · constructor
        · intro h
          have h' : c < guardedEnv H pred r y := h
          rw [hin y hy, h0 y] at h'
          exact Or.inl ⟨hy, h'⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · have h' : c < 0 := h
            show c < guardedEnv H pred r y
            rw [hin y hy, h0 y]
            exact h'
          · exact absurd hy h
      · constructor
        · intro h
          have h' : c < guardedEnv H pred r y := h
          rw [hout y hy] at h'
          exact Or.inr ⟨hy, h'⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h hy
          · have h' : c < 1 := h
            show c < guardedEnv H pred r y
            rw [hout y hy]
            exact h'
    rw [this]
    exact (hNm.inter (MeasurableSet.const _)).union (hNm.compl.inter (MeasurableSet.const _))
  · set O : Set (X → ℕ → ℝ) := ⋃ p : {p : U × (X → ℝ) // p.1 ∈ H ∧ ∀ x, 0 < p.2 x},
      {y | c < batchDens r (fun x => pred x p.1.1) p.1.2 y} with hO
    have hOo : IsOpen O :=
      isOpen_iUnion fun p => isOpen_lt continuous_const (continuous_batchDens r _ _)
    have : guardedEnv H pred r ⁻¹' Set.Ioi c = (N ∩ O) ∪ (Nᶜ ∩ {_y | c < 1}) := by
      ext y
      by_cases hy : y ∈ N
      · constructor
        · intro h
          have h' : c < guardedEnv H pred r y := h
          rw [hin y hy] at h'
          obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup h'
          exact Or.inl ⟨hy, Set.mem_iUnion.mpr ⟨p, hp⟩⟩
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · obtain ⟨p, hp⟩ := Set.mem_iUnion.mp h
            have hp' : c < batchDens r (fun x => pred x p.1.1) p.1.2 y := hp
            show c < guardedEnv H pred r y
            rw [hin y hy]
            exact lt_of_lt_of_le hp' (le_ciSup (nullEnv_bddAbove H pred hy) p)
          · exact absurd hy h
      · constructor
        · intro h
          have h' : c < guardedEnv H pred r y := h
          rw [hout y hy] at h'
          exact Or.inr ⟨hy, h'⟩
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h hy
          · have h' : c < 1 := h
            show c < guardedEnv H pred r y
            rw [hout y hy]
            exact h'
    rw [this]
    exact (hNm.inter hOo.measurableSet).union (hNm.compl.inter (MeasurableSet.const _))

end Guarded

/-! #### The canonical tracker -/

variable {A Z U : Type*}

lemma canon_exists (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty) (H : A → Z → Set U)
    (pred : X → U → ℝ) (k : ℕ) (a : A) (q : (X → ℝ) × (X → ℝ)) :
    ∃ n, q ∉ posSet X ∨ actGameStar (J a) (hJ a) (H a) pred q.1 q.2 ≤
      actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2 + 1 / ((k : ℝ) + 1) := by
  by_cases hq : q ∈ posSet X
  · obtain ⟨n, hn⟩ := exists_near_opt (J a) (hJ a) (H a) pred (m := q.1) hq
      (e := 1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨n, Or.inr hn⟩
  · exact ⟨0, Or.inl hq⟩

open Classical in
/-- The index of the design returned at refresh `k` for action `a`: the first design of the
dense sequence that is `e_k`-optimal at the estimates. -/
def canonIdx (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty) (H : A → Z → Set U)
    (pred : X → U → ℝ) (k : ℕ) (a : A) (q : (X → ℝ) × (X → ℝ)) : ℕ :=
  Nat.find (canon_exists J hJ H pred k a q)

/-- A tracker for arbitrary problem data `(J, H, pred)`: the design oracle returns the first
`e_k`-optimal design of a dense sequence and displays its exact value, ties are broken by
lowest index, rounding is `b_j + ⌊M_j wₓ⌋` with the remainder given to one type, and the
certified bounds are exact (`qlo = q`, and `Uhi = U` on nondegenerate batches, `Uhi = 1` on
degenerate ones). -/
def Tracker.canonical [Fintype A] (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty)
    (H : A → Z → Set U) (pred : X → U → ℝ) (init : A) : Tracker X A Z U where
  J := J
  hJ := hJ
  H := H
  pred := pred
  design k m v a := canonDense X (canonIdx J hJ H pred k a (m, v))
  score k m v a := posExt (fun q => actGame (J a) (hJ a) (H a) pred
    (canonDense X (canonIdx J hJ H pred k a q)) q.1 q.2) (m, v)
  pick := haveI : Nonempty A := ⟨init⟩; canonPick
  alloc := canonAlloc (Classical.arbitrary X)
  qlo _ r mh vh y := batchDens r mh vh y
  Uhi a z _ r _ _ y := guardedEnv (H a z) pred r y
  init := init

/-- **The oracle contracts are satisfiable** for every problem data with nonempty component
nulls. -/
theorem Tracker.canonical_contract [Fintype A] (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty)
    (H : A → Z → Set U) (pred : X → U → ℝ) (init : A)
    (hH : ∀ a, ∀ z ∈ J a, (H a z).Nonempty) :
    (Tracker.canonical J hJ H pred init).Contract := by
  classical
  refine
    { H_nonempty := hH
      design_mem := fun k m v a => canonDense_mem _
      score_le := fun k m v a hv => ?_
      star_le := fun k m v a hv => ?_
      pick_max := fun f b => ?_
      alloc_sum := fun j w hw => canonAlloc_sum _ j hw
      alloc_base := fun j w x _ => ?_
      alloc_dom := fun j w x _ => canonAlloc_dom _ j w x
      qlo_nonneg := fun j r mh vh y => batchDens_nonneg r mh vh y
      Uhi_nonneg := fun a z j r mh vh y => guardedEnv_nonneg _ _ _ _
      qlo_pos := fun j r mh vh y hvh => batchDens_pos r mh hvh y
      qlo_le := fun j r mh vh y _ => le_rfl
      Uhi_ge := fun a z j r mh vh y _ hnd => le_of_eq (guardedEnv_of_nondeg hnd).symm
      two_nat := fun a z j r mh vh y _ _ hnd => ?_ }
  · have hq : ((m, v) : (X → ℝ) × (X → ℝ)) ∈ posSet X := hv
    exact le_of_eq (posExt_of_mem (F := fun q => actGame (J a) (hJ a) (H a) pred
      (canonDense X (canonIdx J hJ H pred k a q)) q.1 q.2) hq)
  · have hq : ((m, v) : (X → ℝ) × (X → ℝ)) ∈ posSet X := hv
    have hs := Nat.find_spec (canon_exists J hJ H pred k a (m, v))
    have hsc : (Tracker.canonical J hJ H pred init).score k m v a =
        actGame (J a) (hJ a) (H a) pred
          (canonDense X (canonIdx J hJ H pred k a (m, v))) m v :=
      posExt_of_mem (F := fun q => actGame (J a) (hJ a) (H a) pred
      (canonDense X (canonIdx J hJ H pred k a q)) q.1 q.2) hq
    rw [hsc]
    rcases hs with hs | hs
    · exact absurd hq hs
    · exact hs
  · have : Nonempty A := ⟨init⟩
    exact (canonPick_spec f).1 b
  · show baseB j ≤ canonAlloc _ j w x
    unfold canonAlloc
    omega
  · have hlog : ∀ t : ℝ, Real.log (t / t) ≤ 0 := by
      intro t
      by_cases ht : t = 0
      · rw [ht, div_zero, Real.log_zero]
      · rw [div_self ht, Real.log_one]
    have h1 := hlog (batchDens r mh vh y)
    have h2 := hlog (nullEnv (H a z) pred r y)
    show Real.log (batchDens r mh vh y / batchDens r mh vh y) +
      Real.log (guardedEnv (H a z) pred r y / nullEnv (H a z) pred r y) ≤ 2
    rw [guardedEnv_of_nondeg hnd]
    linarith

/-- The allocation oracles of the canonical tracker are measurable. -/
theorem Tracker.canonical_meas [Fintype A] (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty)
    (H : A → Z → Set U) (pred : X → U → ℝ) (init : A) :
    (Tracker.canonical J hJ H pred init).Meas := by
  classical
  have hcontG : ∀ (a : A) (n : ℕ), ContinuousOn (fun q : (X → ℝ) × (X → ℝ) =>
      actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2) (posSet X) := fun a n =>
    continuousOn_of_transport fun m v m' v' d hv hv' hd =>
      actGame_transport (J a) (hJ a) (H a) pred (canonDense_mem n) hv hv' hd
  have hcontS : ∀ a : A, ContinuousOn (fun q : (X → ℝ) × (X → ℝ) =>
      actGameStar (J a) (hJ a) (H a) pred q.1 q.2) (posSet X) := fun a =>
    continuousOn_of_transport fun m v m' v' d hv hv' hd =>
      actGameStar_transport (J a) (hJ a) (H a) pred hv hv' hd
  have hp : ∀ (k : ℕ) (a : A) (n : ℕ), MeasurableSet {q : (X → ℝ) × (X → ℝ) |
      q ∉ posSet X ∨ actGameStar (J a) (hJ a) (H a) pred q.1 q.2 ≤
        actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2 + 1 / ((k : ℝ) + 1)} := by
    intro k a n
    have hE : MeasurableSet {q : (X → ℝ) × (X → ℝ) |
        posExt (fun q => actGameStar (J a) (hJ a) (H a) pred q.1 q.2) q ≤
          posExt (fun q => actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2) q +
            1 / ((k : ℝ) + 1)} :=
      measurableSet_le (measurable_posExt (hcontS a))
        ((measurable_posExt (hcontG a n)).add measurable_const)
    have : {q : (X → ℝ) × (X → ℝ) |
        q ∉ posSet X ∨ actGameStar (J a) (hJ a) (H a) pred q.1 q.2 ≤
          actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2 + 1 / ((k : ℝ) + 1)} =
        (posSet X)ᶜ ∪ (posSet X ∩ {q : (X → ℝ) × (X → ℝ) |
          posExt (fun q => actGameStar (J a) (hJ a) (H a) pred q.1 q.2) q ≤
            posExt (fun q => actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2) q +
              1 / ((k : ℝ) + 1)}) := by
      ext q
      by_cases hq : q ∈ posSet X
      · constructor
        · rintro (h | h)
          · exact absurd hq h
          · refine Or.inr ⟨hq, ?_⟩
            show posExt _ q ≤ posExt _ q + _
            rw [posExt_of_mem hq, posExt_of_mem hq]
            exact h
        · rintro (h | ⟨-, h⟩)
          · exact absurd hq h
          · have h' : posExt (fun q => actGameStar (J a) (hJ a) (H a) pred q.1 q.2) q ≤
                posExt (fun q => actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2) q +
                  1 / ((k : ℝ) + 1) := h
            rw [posExt_of_mem hq, posExt_of_mem hq] at h'
            exact Or.inr h'
      · constructor
        · intro _
          exact Or.inl hq
        · intro _
          exact Or.inl hq
    rw [this]
    exact measurableSet_posSet.compl.union (measurableSet_posSet.inter hE)
  have hidx : ∀ (k : ℕ) (a : A), Measurable (canonIdx J hJ H pred k a) := fun k a =>
    Measurable.find (f := fun n _ => n) (fun _ => measurable_const) (hp k a)
      (canon_exists J hJ H pred k a)
  refine
    { design_meas := fun k a => ?_
      score_meas := fun k a => ?_
      pick_meas := fun a => ?_
      alloc_meas := fun j x => measurable_canonAlloc _ j x }
  · exact Measurable.find (f := fun n _ => canonDense X n) (fun _ => measurable_const) (hp k a)
      (canon_exists J hJ H pred k a)
  · refine measurable_comp_countable (D := canonIdx J hJ H pred k a)
      (fun n => (hidx k a) (measurableSet_singleton n))
      (Ψ := fun n => posExt fun q => actGame (J a) (hJ a) (H a) pred (canonDense X n) q.1 q.2)
      (fun n => measurable_posExt (hcontG a n)) (fun q => ?_)
    rfl
  · have : Nonempty A := ⟨init⟩
    exact measurableSet_canonPick a

/-- The certified bounds of the canonical tracker are adapted, for every pair `(a, z)`. -/
theorem Tracker.canonical_boundsAdapted [Fintype A] (J : A → Finset Z)
    (hJ : ∀ a, (J a).Nonempty) (H : A → Z → Set U) (pred : X → U → ℝ) (init : A) (a : A)
    (z : Z) : (Tracker.canonical J hJ H pred init).BoundsAdapted a z where
  qlo_meas := fun _ r => measurable_batchDens_joint r
  Uhi_meas := fun _ r => by
    have h := (measurable_guardedEnv (H a z) pred r).comp
      ((measurable_snd.comp measurable_snd :
        Measurable fun p : (X → ℝ) × (X → ℝ) × (X → ℕ → ℝ) => p.2.2))
    exact h
  qlo_local := fun _ _ _ _ _ _ h => batchDens_congr h
  Uhi_local := fun _ _ _ _ _ _ h => guardedEnv_congr (H a z) pred h

end Instance

/-! ### The theorem for the tracker -/

section Final

variable {Ω : Type*} [MeasurableSpace Ω] {X A Z U : Type*} [Fintype X] [Nonempty X]
  [DecidableEq X] [Fintype A] [DecidableEq A]

/-- **Sparse four-power nuisance-KL tracking with unknown variances (Theorem
`thm:v34-adaptive`), for the formal tracker on intrinsic tapes.**

Hypotheses, all on the model.

* The tracker `T` satisfies the oracle contracts of the manuscript (`Tracker.Contract`) and its
  allocation oracles (design, displayed score, tie-breaking, rounding) are Borel
  (`Tracker.Meas`).  Both are satisfiable for every problem data
  (`Tracker.canonical_contract`, `Tracker.canonical_meas`).
* The observations `Y x n` are jointly independent with `Y x n ~ N(pred x θ, vₓ)`, `vₓ > 0`.
* `C = C_* = max_a C_a^*(μ, v) > 0` at the true means `μₓ = pred x θ`.

Conclusions.

* `(ε, δ)`-correctness: for every `δ > 0`, the probability that at some batch the stopping test
  passes while the selected action is incorrect (`θ` lies in one of its closed invalidating
  nulls `H a z`, `z ∈ J a`) is at most `δ`.
* The sharp rate `eq:v34-sharp-rate`, as in `v34_adaptive_rate`: for every rational
  `s ∈ (0, 1]` a constant `D_s ≥ 0` independent of `δ` with
  `E τ_δ ≤ D_s + (1 + s) / C_* · log (1 / δ)` for `δ ∈ (0, 1)`, and for every `c > 1 / C_*`
  eventually `E τ_δ ≤ c log (1 / δ)` as `δ ↓ 0`.  Here
  `E τ_δ = E ∑_j R_{j+1} 1{τ_δ > N_j}` (lower integral). -/
theorem v34_adaptive (T : Tracker X A Z U) (hc : T.Contract) (hm : T.Meas) (P : Measure Ω)
    [IsProbabilityMeasure P] (θ : U) {v : X → ℝ} (hv0 : ∀ x, 0 < v x) {Y : X → ℕ → Ω → ℝ}
    (hind : iIndepFun (fun (p : X × ℕ) => Y p.1 p.2) P)
    (hY : ∀ x n, HasLaw (Y x n) (gaussianReal (T.pred x θ) (v x).toNNReal) P) {C : ℝ}
    (hC : 0 < C)
    (hCmax : ∀ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred (fun x => T.pred x θ) v ≤ C)
    (hCatt : ∃ a, actGameStar (T.J a) (T.hJ a) (T.H a) T.pred (fun x => T.pred x θ) v = C) :
    (∀ δ : ℝ, 0 < δ →
      P {ω | ∃ j, (∃ z ∈ T.J (T.sel (fun x n => Y x n ω) j),
          θ ∈ T.H (T.sel (fun x n => Y x n ω) j) z) ∧ T.test (fun x n => Y x n ω) δ j} ≤
        ENNReal.ofReal δ) ∧
    (∀ s : ℚ, 0 < s → s ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧ ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∫⁻ ω, ∑' j, ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) *
          {ω | T.running (fun x n => Y x n ω) δ j}.indicator 1 ω ∂P ≤
        ENNReal.ofReal (D + (1 + (s : ℝ)) / C * Real.log (1 / δ))) ∧
    ∀ c : ℝ, 1 / C < c → ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, ∑' j, ENNReal.ofReal (batchR (Fintype.card X) (j + 1)) *
          {ω | T.running (fun x n => Y x n ω) δ j}.indicator 1 ω ∂P).toReal ≤
        c * Real.log (1 / δ) := by
  have hindx : ∀ x, iIndepFun (Y x) P := fun x =>
    hind.precomp (g := fun n : ℕ => ((x, n) : X × ℕ)) fun n n' h => (Prod.mk.inj h).2
  exact ⟨fun δ hδ => T.coverage hc hm P hind θ hv0 hY hδ,
    v34_adaptive_rate T hc P hv0 hindx hY hC hCmax hCatt⟩

omit [DecidableEq X] [DecidableEq A] in
/-- **Theorem `thm:v34-adaptive` is not vacuous**: for every problem data with nonempty
component nulls there is a tracker (`Tracker.canonical`) satisfying the oracle contracts and
the measurability requirement, hence the conclusions of `v34_adaptive`; its certified bounds
are moreover adapted, so `Tracker.wealth_supermartingale` applies to it. -/
theorem exists_tracker_contract_meas (J : A → Finset Z) (hJ : ∀ a, (J a).Nonempty)
    (H : A → Z → Set U) (pred : X → U → ℝ) (init : A)
    (hH : ∀ a, ∀ z ∈ J a, (H a z).Nonempty) :
    ∃ T : Tracker X A Z U, T.J = J ∧ T.H = H ∧ T.pred = pred ∧ T.init = init ∧
      T.Contract ∧ T.Meas ∧ ∀ a z, T.BoundsAdapted a z :=
  ⟨Tracker.canonical J hJ H pred init, rfl, rfl, rfl, rfl,
    Tracker.canonical_contract J hJ H pred init hH, Tracker.canonical_meas J hJ H pred init,
    Tracker.canonical_boundsAdapted J hJ H pred init⟩

end Final

end

end JointRootCert
