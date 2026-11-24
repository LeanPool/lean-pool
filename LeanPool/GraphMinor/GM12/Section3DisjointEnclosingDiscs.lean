/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SurroundingDisc
import LeanPool.GraphMinor.Surface.DiscsInSurface
import LeanPool.GraphMinor.GM12.Section3DiscUniqueness
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Disjoint enclosing discs away from the sphere

For the first two-loop shape in XII (3.1), page 245, disjoint circles
surrounding distinct cuffs bound disjoint discs. On a surface other
than the sphere, disc uniqueness proves this: nested boundaries force
nested discs, which would enclose both prescribed deleted discs.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Two discs which do not cover the surface and have disjoint
boundaries are disjoint unless one includes the other. -/
theorem disjoint_discs_of_disjoint_boundaries_of_not_nested_of_noncover
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbd : Disjoint (discBd D) (discBd E))
    (hDE : ¬ D ⊆ E) (hED : ¬ E ⊆ D) (hcover : D ∪ E ≠ univ) : Disjoint D E := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hbE : Disjoint (discBd E) D := by
    rcases hD.side hman hE.isOArc_discBd.isPreconnected hbd.symm with hin | hout
    · obtain ⟨E', hE', _⟩ := disc_oArc D (discBd E) hD
        (hin.trans (discInt_subset D)) hE.isOArc_discBd
      have hcover' : E ∪ E' ≠ univ := by
        intro he
        apply hcover
        apply eq_univ_of_univ_subset
        rw [← he]
        exact union_subset subset_union_right (hE'.1.trans subset_union_left)
      have heq : E = E' := eq_of_discBd_eq_of_union_ne_univ hman hE hE'.2.1
        hE'.2.2.1.symm hcover'
      exact False.elim (hED (heq ▸ hE'.1))
    · exact hout
  rcases hE.side hman hD.isPathConnected.isConnected.isPreconnected hbE.symm with hin | hout
  · exact False.elim (hDE (hin.trans (discInt_subset E)))
  · exact hout

/-- On a surface other than the sphere, two discs with disjoint
boundaries are disjoint unless one includes the other. -/
theorem disjoint_discs_of_disjoint_boundaries_of_not_nested
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hbd : Disjoint (discBd D) (discBd E))
    (hDE : ¬ D ⊆ E) (hED : ¬ E ⊆ D) : Disjoint D E := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hsurf : IsSurface S := ⟨hS.1, hS.2.1, hman⟩
  have hbE : Disjoint (discBd E) D := by
    rcases hD.side hman hE.isOArc_discBd.isPreconnected hbd.symm with hin | hout
    · obtain ⟨E', hE', _⟩ := disc_oArc D (discBd E) hD
        (hin.trans (discInt_subset D)) hE.isOArc_discBd
      have heq : E = E' := eq_of_discBd_eq hsurf hns hE hE'.2.1 hE'.2.2.1.symm
      exact False.elim (hED (heq ▸ hE'.1))
    · exact hout
  rcases hE.side hman hD.isPathConnected.isConnected.isPreconnected hbE.symm with hin | hout
  · exact False.elim (hDE (hin.trans (discInt_subset E)))
  · exact hout

/-- Disjoint circles surrounding distinct prescribed cuffs bound
disjoint enclosing discs when the original surface is not a sphere.
These are the discs required by XII (3.1)(ii). -/
theorem exists_disjoint_surrounding_discs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {i j : ι} (hij : i ≠ j) {F₁ F₂ : Set (discComplement Δ)}
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hFF : Disjoint F₁ F₂)
    (hs₁ : GM07.SurroundsCuff F₁ (Subtype.val ⁻¹' discBd (Δ i)))
    (hs₂ : GM07.SurroundsCuff F₂ (Subtype.val ⁻¹' discBd (Δ j))) :
    ∃ D E : Set S, IsClosedDisc D ∧ IsClosedDisc E ∧
      discBd D = (Subtype.val : discComplement Δ → S) '' F₁ ∧
      discBd E = (Subtype.val : discComplement Δ → S) '' F₂ ∧
      (∀ k, Δ k ⊆ D ↔ k = i) ∧ (∀ k, Δ k ⊆ E ↔ k = j) ∧ Disjoint D E := by
  obtain ⟨D, hD, hbD, honeD⟩ :=
    surrounding_bounds_disc_including_exactly_one hS Δ hΔ hdisj i hF₁ hs₁
  obtain ⟨E, hE, hbE, honeE⟩ :=
    surrounding_bounds_disc_including_exactly_one hS Δ hΔ hdisj j hF₂ hs₂
  refine ⟨D, E, hD, hE, hbD, hbE, honeD, honeE, ?_⟩
  apply disjoint_discs_of_disjoint_boundaries_of_not_nested hS hns hD hE
  · rw [hbD, hbE]
    apply Set.disjoint_left.mpr
    rintro x ⟨y, hy, rfl⟩ ⟨z, hz, he⟩
    have hzy := Subtype.val_injective he
    exact Set.disjoint_left.mp hFF hy (hzy ▸ hz)
  · intro hDE
    exact hij ((honeE i).mp (((honeD i).mpr rfl).trans hDE))
  · intro hED
    exact hij (((honeD j).mp (((honeE j).mpr rfl).trans hED)).symm)

end GraphMinor.GM12
