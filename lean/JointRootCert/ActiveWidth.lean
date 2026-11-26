/-
Width charged to each selected terminal (Lemmas `lem:active-width` and
`lem:active-os-width`, Appendix B.3).

These are the per-step facts behind the finite-sample bounds of Theorem `thm:active-er`:
whenever an active sampler continues, the terminal it queries still has a wide
confidence interval, both in absolute terms and relative to its own gap
`Δ_z = μ_* - μ_z`.  Interval widths are `w z = u z - l z`.
-/
import JointRootCert.Acquisition

namespace JointRootCert

open Finset

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z] {A : Type*}
variable {l u : Z → ℝ} {ε : ℝ}

/-- An action that retains a terminal with globally maximal upper endpoint has
certificate at most that terminal's interval width. -/
lemma rectCert_le_width {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hlu : l ≤ u)
    {g : Z} (hgS : g ∈ S) (hg : ∀ x, u x ≤ u g) : rectCert S hS hSc l u ≤ u g - l g := by
  unfold rectCert
  refine max_le (sub_nonneg.mpr (hlu g)) (sub_le_sub (sup'_le _ _ (fun x _ => hg x)) ?_)
  exact le_sup' l hgS

/-- **Width charged to each selected terminal (Lemma `lem:active-width`).**

`a` minimises the exact certificate and the procedure continues (`ε < R(a)`); `p` and `q`
are the optimistic inside and outside witnesses of `a`.  Then

* the wider of the two witnesses has width greater than `ε`, without any coverage
  assumption;
* if the true means lie in the box, whichever witness is the wider one (and is therefore
  queried) has width at least half its own gap. -/
theorem active_width (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) (hlu : l ≤ u) (hε : 0 ≤ ε)
    (a : A)
    (hmin : ∀ c, rectCert (supp a) (hne a) (hpr a) l u ≤ rectCert (supp c) (hne c) (hpr c) l u)
    (hcont : ε < rectCert (supp a) (hne a) (hpr a) l u)
    {p q : Z} (hp : p ∈ supp a) (hpmax : ∀ y ∈ supp a, u y ≤ u p)
    (hq : q ∉ supp a) (hqmax : ∀ z, z ∉ supp a → u z ≤ u q) :
    ε < max (u p - l p) (u q - l q) ∧
      ∀ μ ∈ Set.Icc l u,
        (u q - l q ≤ u p - l p → (gmax μ - μ p) / 2 ≤ u p - l p) ∧
        (u p - l p ≤ u q - l q → (gmax μ - μ q) / 2 ≤ u q - l q) := by
  have hUq : (supp a)ᶜ.sup' (hpr a) u = u q :=
    le_antisymm (sup'_le _ _ (fun z hz => hqmax z (mem_compl.mp hz)))
      (le_sup' u (mem_compl.mpr hq))
  have hLp : l p ≤ (supp a).sup' (hne a) l := le_sup' l hp
  have hLu : (supp a).sup' (hne a) l ≤ u p :=
    sup'_le _ _ (fun y hy => (hlu y).trans (hpmax y hy))
  have hRa : rectCert (supp a) (hne a) (hpr a) l u =
      max 0 (u q - (supp a).sup' (hne a) l) := by
    unfold rectCert
    rw [hUq]
  have hgap : ε < u q - (supp a).sup' (hne a) l := by
    by_contra h
    have : max 0 (u q - (supp a).sup' (hne a) l) ≤ ε := max_le hε (not_lt.mp h)
    rw [hRa] at hcont
    linarith
  have hRa' : rectCert (supp a) (hne a) (hpr a) l u = u q - (supp a).sup' (hne a) l := by
    rw [hRa]
    exact max_eq_right (by linarith)
  rcases le_total (u q) (u p) with hpq | hpq
  · -- the inside witness has the globally largest upper endpoint
    have hg : ∀ x, u x ≤ u p := fun x => by
      by_cases hx : x ∈ supp a
      · exact hpmax x hx
      · exact (hqmax x hx).trans hpq
    have hw : rectCert (supp a) (hne a) (hpr a) l u ≤ u p - l p :=
      rectCert_le_width (hne a) (hpr a) hlu hp hg
    refine ⟨lt_of_lt_of_le (lt_of_lt_of_le hcont hw) (le_max_left _ _), fun μ hμ => ?_⟩
    have hstar : gmax μ ≤ u p := sup'_le _ _ (fun x _ => (hμ.2 x).trans (hg x))
    have h1 := hμ.1 p
    have h2 := hμ.1 q
    have h3 := le_gmax μ p
    have h4 := le_gmax μ q
    constructor
    · intro _
      linarith
    · intro hsel
      linarith
  · -- the outside witness has the globally largest upper endpoint
    have hg : ∀ x, u x ≤ u q := fun x => by
      by_cases hx : x ∈ supp a
      · exact (hpmax x hx).trans hpq
      · exact hqmax x hx
    obtain ⟨c, hc⟩ := hcov q
    have hw : rectCert (supp a) (hne a) (hpr a) l u ≤ u q - l q :=
      (hmin c).trans (rectCert_le_width (hne c) (hpr c) hlu hc hg)
    refine ⟨lt_of_lt_of_le (lt_of_lt_of_le hcont hw) (le_max_right _ _), fun μ hμ => ?_⟩
    have hstar : gmax μ ≤ u q := sup'_le _ _ (fun x _ => (hμ.2 x).trans (hg x))
    have h1 := hμ.1 p
    have h2 := hμ.1 q
    have h3 := le_gmax μ p
    have h4 := le_gmax μ q
    rw [hRa'] at hw
    constructor
    · intro hsel
      linarith
    · intro _
      linarith

/-- The optimistic-separation index `J(a) = U(a) - L⁻(a)`: optimistic inside value minus
pessimistic outside value. -/
noncomputable def osIndex (S : Finset Z) (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    (l u : Z → ℝ) : ℝ :=
  S.sup' hS u - Sᶜ.sup' hSc l

/-- On coverage the index is at least the true separation `V(a) - max_{z ∉ S(a)} μ_z`. -/
lemma le_osIndex {S : Finset Z} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) {μ : Z → ℝ}
    (hμ : μ ∈ Set.Icc l u) : val S hS μ - Sᶜ.sup' hSc μ ≤ osIndex S hS hSc l u := by
  unfold osIndex val
  refine sub_le_sub ?_ ?_
  · exact sup'_le _ _ (fun y hy => (hμ.2 y).trans (le_sup' u hy))
  · exact sup'_le _ _ (fun z hz => (hμ.1 z).trans (le_sup' μ hz))

/-- **Width charged by optimistic-separation sampling (Lemma `lem:active-os-width`).**

`b` maximises the index `J`, the global stopping test failed (`ε < R(b)`), and `p`, `q`
are the optimistic inside and outside witnesses of `b`.  Then

* the wider witness has width greater than `ε / 2`, without coverage;
* on coverage it has width greater than `(Γ + ε) / 2` for the separation
  `Γ = V(a) - max_{z ∉ S(a)} μ_z` of every action `a`, hence for the largest one;
* on coverage the queried (wider) witness has width at least half its own gap. -/
theorem active_os_width (supp : A → Finset Z) (hne : ∀ a, (supp a).Nonempty)
    (hpr : ∀ a, (supp a)ᶜ.Nonempty) (hcov : ∀ z, ∃ a, z ∈ supp a) (hlu : l ≤ u) (hε : 0 ≤ ε)
    (b : A)
    (hmax : ∀ c, osIndex (supp c) (hne c) (hpr c) l u ≤ osIndex (supp b) (hne b) (hpr b) l u)
    (hcont : ε < rectCert (supp b) (hne b) (hpr b) l u)
    {p q : Z} (hp : p ∈ supp b) (hpmax : ∀ y ∈ supp b, u y ≤ u p)
    (hq : q ∉ supp b) (hqmax : ∀ z, z ∉ supp b → u z ≤ u q) :
    ε / 2 < max (u p - l p) (u q - l q) ∧
      ∀ μ ∈ Set.Icc l u,
        (∀ a, (val (supp a) (hne a) μ - (supp a)ᶜ.sup' (hpr a) μ + ε) / 2 <
          max (u p - l p) (u q - l q)) ∧
        (u q - l q ≤ u p - l p → (gmax μ - μ p) / 2 ≤ u p - l p) ∧
        (u p - l p ≤ u q - l q → (gmax μ - μ q) / 2 ≤ u q - l q) := by
  have hUq : (supp b)ᶜ.sup' (hpr b) u = u q :=
    le_antisymm (sup'_le _ _ (fun z hz => hqmax z (mem_compl.mp hz)))
      (le_sup' u (mem_compl.mpr hq))
  have hUp : (supp b).sup' (hne b) u = u p :=
    le_antisymm (sup'_le _ _ (fun y hy => hpmax y hy)) (le_sup' u hp)
  have hLp : l p ≤ (supp b).sup' (hne b) l := le_sup' l hp
  have hLq : l q ≤ (supp b)ᶜ.sup' (hpr b) l := le_sup' l (mem_compl.mpr hq)
  have hgap : ε < u q - (supp b).sup' (hne b) l := by
    by_contra h
    have : rectCert (supp b) (hne b) (hpr b) l u ≤ ε := by
      unfold rectCert
      rw [hUq]
      exact max_le hε (not_lt.mp h)
    linarith
  -- the index of `b` is below the sum of the two widths minus `ε`
  have hJ : osIndex (supp b) (hne b) (hpr b) l u < (u p - l p) + (u q - l q) - ε := by
    unfold osIndex
    rw [hUp]
    linarith
  have hsum : (u p - l p) + (u q - l q) ≤ 2 * max (u p - l p) (u q - l q) := by
    have := le_max_left (u p - l p) (u q - l q)
    have := le_max_right (u p - l p) (u q - l q)
    linarith
  -- the index of `b` is nonnegative: some action retains a globally upper-maximal terminal
  have hJ0 : 0 ≤ osIndex (supp b) (hne b) (hpr b) l u := by
    obtain ⟨g, -, hgmax⟩ := exists_mem_eq_sup' (univ_nonempty (α := Z)) u
    have hg : ∀ x, u x ≤ u g := fun x => hgmax ▸ le_sup' u (mem_univ x)
    obtain ⟨c, hc⟩ := hcov g
    refine le_trans ?_ (hmax c)
    unfold osIndex
    have h1 : u g ≤ (supp c).sup' (hne c) u := le_sup' u hc
    have h2 : (supp c)ᶜ.sup' (hpr c) l ≤ u g := sup'_le _ _ (fun z _ => (hlu z).trans (hg z))
    linarith
  refine ⟨by linarith, fun μ hμ => ⟨fun a => ?_, ?_, ?_⟩⟩
  · have h1 := le_osIndex (hne a) (hpr a) hμ
    have h2 := hmax a
    linarith
  · intro hsel
    have h1 := hμ.1 p
    have h3 := le_gmax μ p
    rcases le_total (u q) (u p) with hpq | hpq
    · have hstar : gmax μ ≤ u p := sup'_le _ _ (fun x _ => (hμ.2 x).trans (by
        by_cases hx : x ∈ supp b
        · exact hpmax x hx
        · exact (hqmax x hx).trans hpq))
      linarith
    · have hstar : gmax μ ≤ u q := sup'_le _ _ (fun x _ => (hμ.2 x).trans (by
        by_cases hx : x ∈ supp b
        · exact (hpmax x hx).trans hpq
        · exact hqmax x hx))
      unfold osIndex at hJ0
      rw [hUp] at hJ0
      linarith
  · intro hsel
    have h2 := hμ.1 q
    have h4 := le_gmax μ q
    rcases le_total (u q) (u p) with hpq | hpq
    · have hstar : gmax μ ≤ u p := sup'_le _ _ (fun x _ => (hμ.2 x).trans (by
        by_cases hx : x ∈ supp b
        · exact hpmax x hx
        · exact (hqmax x hx).trans hpq))
      linarith
    · have hstar : gmax μ ≤ u q := sup'_le _ _ (fun x _ => (hμ.2 x).trans (by
        by_cases hx : x ∈ supp b
        · exact (hpmax x hx).trans hpq
        · exact hqmax x hx))
      linarith

end JointRootCert
