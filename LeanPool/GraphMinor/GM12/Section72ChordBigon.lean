/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
public import LeanPool.GraphMinor.GM11.RadialChord
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A chord cuts off a disc outside a nested disc

For the equal-vertex case of the radial condition in XII (7.2),
page 260, the removed spoke is a chord of a possible new empty bigon.
Cut along that chord. The connected open interior of the removed disc
lies on one side of it. The other side is a closed disc outside that
open interior, bounded by the removed spoke and one of the two old
boundary spokes.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The chord argument for the equal-vertex case of the radial
condition in XII (7.2), page 260. One side of the chord misses the
open interior of the nested disc. -/
theorem exists_chord_bigon_outside_nested_disc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {D Q F G H : Set S} {v u : S}
    (hD : IsClosedDisc D) (hQ : IsClosedDisc Q) (hDQ : D ⊆ Q)
    (hF : IsLineWithEnds F v u) (hG : IsLineWithEnds G v u)
    (hH : IsLineWithEnds H v u) (hvu : v ≠ u)
    (hFbd : F ⊆ discBd D) (hbdQ : discBd Q = G ∪ H)
    (hGH : G ∩ H ⊆ {v, u}) (hFQ : F ∩ discBd Q = {v, u}) :
    ∃ P : Set S, IsClosedDisc P ∧ P ⊆ Q ∧
      (discBd P = G ∪ F ∨ discBd P = H ∪ F) ∧ Disjoint (discInt D) P := by
  have hFQsub : F ⊆ Q := hFbd.trans ((Surface.discBd_subset D).trans hDQ)
  obtain ⟨A₁, A₂, Q₁, Q₂, _, hcomp, hQ₁, hQ₂, hUnion, hInter, hbd₁, hbd₂, _⟩ :=
    disc_iArc Q F v u hQ hFQsub hvu hF hFQ
  have hparts : componentsIn (discBd Q \ {v, u}) = {G \ {v, u}, H \ {v, u}} := by
    rw [hbdQ, union_sdiff_distrib]
    apply componentsIn_union_eq_pair
      (isPathConnected_sdiff_pair hG).isConnected.isPreconnected
      (isPathConnected_sdiff_pair hH).isConnected.isPreconnected
      (isPathConnected_sdiff_pair hG).nonempty
      (isPathConnected_sdiff_pair hH).nonempty
    · rw [closure_sdiff_pair hG]
      exact disjoint_left.mpr fun x hxG hxH => hxH.2 (hGH ⟨hxG, hxH.1⟩)
    · rw [closure_sdiff_pair hH]
      exact disjoint_left.mpr fun x hxG hxH => hxG.2 (hGH ⟨hxG.1, hxH⟩)
  have hends : ({v, u} : Set S) ⊆ F := fun x hx => (hFQ.superset hx).1
  have hrestore : ∀ L : Set S, (L \ {v, u}) ∪ F = L ∪ F := by
    intro L
    ext x
    constructor
    · rintro (hx | hx)
      · exact Or.inl hx.1
      · exact Or.inr hx
    · rintro (hx | hx)
      · by_cases he : x ∈ ({v, u} : Set S)
        · exact Or.inr (hends he)
        · exact Or.inl ⟨hx, he⟩
      · exact Or.inr hx
  have hbds : (discBd Q₁ = G ∪ F ∨ discBd Q₁ = H ∪ F) ∧
      (discBd Q₂ = G ∪ F ∨ discBd Q₂ = H ∪ F) := by
    have ha₁ : A₁ ∈ componentsIn (discBd Q \ {v, u}) := hcomp.superset (Or.inl rfl)
    have ha₂ : A₂ ∈ componentsIn (discBd Q \ {v, u}) := hcomp.superset (Or.inr rfl)
    rw [hparts] at ha₁ ha₂
    constructor
    · rcases ha₁ with h | h
      · exact Or.inl (hbd₁.trans (h ▸ hrestore G))
      · exact Or.inr (hbd₁.trans (h ▸ hrestore H))
    · rcases ha₂ with h | h
      · exact Or.inl (hbd₂.trans (h ▸ hrestore G))
      · exact Or.inr (hbd₂.trans (h ▸ hrestore H))
  have hsub : discInt D ⊆ Q₁ ∪ Q₂ := hUnion.symm ▸ ((discInt_subset D).trans hDQ)
  have hseparate : ∀ x ∈ discInt D, x ∈ Q₁ → x ∉ Q₂ := by
    intro x hxD hx₁ hx₂
    exact hxD.2 (hFbd (hInter.subset ⟨hx₁, hx₂⟩))
  rcases subset_or_subset_of_closed hD.isPreconnected_discInt hQ₁.isClosed hQ₂.isClosed
      hsub hseparate with hin₁ | hin₂
  · refine ⟨Q₂, hQ₂, ?_, hbds.2, ?_⟩
    · exact fun x hx => hUnion ▸ Or.inr hx
    · exact disjoint_left.mpr fun x hxD hx₂ => hseparate x hxD (hin₁ hxD) hx₂
  · refine ⟨Q₁, hQ₁, ?_, hbds.1, ?_⟩
    · exact fun x hx => hUnion ▸ Or.inl hx
    · exact disjoint_left.mpr fun x hxD hx₁ => hseparate x hxD hx₁ (hin₂ hxD)

end GraphMinor.GM12
