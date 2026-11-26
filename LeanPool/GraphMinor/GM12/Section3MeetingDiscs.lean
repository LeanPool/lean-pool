/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DiscUniqueness
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.Circle

/-!
# Discs whose boundaries meet at one point

For XII (3.1)(iii), page 245, two surrounding circles meet at one
point. Removing that point leaves each circle connected. Disc
separation and uniqueness then show that nonnested enclosing discs
meet only at that point.
-/

public section

namespace GraphMinor.GM12

open Set Surface

variable {S : Type*} [TopologicalSpace S]

/-- Removing one point from a circle leaves a path-connected set. -/
theorem isPathConnected_oArc_diff {F : Set S} (hF : IsOArc F) {u : S} (hu : u ∈ F) :
    IsPathConnected (F \ {u}) :=
  hF.isPathConnected_sdiff_singleton hu

private theorem discInt_disjoint_of_boundaries_meet_once
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {D E : Set S} {u : S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hcap : discBd D ∩ discBd E = {u})
    (hDE : ¬ D ⊆ E) (hED : ¬ E ⊆ D)
    (hcase : ¬ IsSphere S ∨ D ∪ E ≠ univ) : Disjoint (discInt D) E := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hu : u ∈ discBd D ∩ discBd E := hcap.symm ▸ mem_singleton u
  have hmiss : Disjoint (discBd E \ {u}) (discBd D) := by
    apply Set.disjoint_left.mpr
    intro x hxE hxD
    have hx : x ∈ discBd D ∩ discBd E := ⟨hxD, hxE.1⟩
    rw [hcap] at hx
    exact hxE.2 hx
  have hout : Disjoint (discBd E \ {u}) D := by
    rcases hD.side hman (isPathConnected_oArc_diff hE.isOArc_discBd hu.2).isConnected.isPreconnected
      hmiss with hin | hout
    · have hbED : discBd E ⊆ D := by
        intro x hx
        by_cases hxu : x = u
        · exact hxu ▸ discBd_subset D hu.1
        · exact (hin ⟨hx, hxu⟩).1
      obtain ⟨E', hE', _⟩ := disc_oArc D (discBd E) hD hbED hE.isOArc_discBd
      have heq : E = E' := by
        rcases hcase with hns | hnoncover
        · exact eq_of_discBd_eq ⟨hS.1, hS.2.1, hman⟩ hns hE hE'.2.1 hE'.2.2.1.symm
        · apply eq_of_discBd_eq_of_union_ne_univ hman hE hE'.2.1 hE'.2.2.1.symm
          intro he
          apply hnoncover
          apply eq_univ_of_univ_subset
          rw [← he]
          exact union_subset subset_union_right (hE'.1.trans subset_union_left)
      exact False.elim (hED (heq ▸ hE'.1))
    · exact hout
  have hmiss' : Disjoint (discInt D) (discBd E) := by
    apply Set.disjoint_left.mpr
    intro x hxD hxE
    by_cases hxu : x = u
    · exact hxD.2 (hxu ▸ hu.1)
    · exact Set.disjoint_left.mp hout ⟨hxE, hxu⟩ hxD.1
  rcases hE.side hman hD.isPreconnected_discInt hmiss' with hin | hout
  · apply False.elim
    apply hDE
    apply hD.subset_closure_discInt.trans
    rw [← hE.isClosed.closure_eq]
    exact closure_mono (hin.trans (discInt_subset E))
  · exact hout

/-- Nonnested enclosing discs whose boundaries meet at one point
meet exactly at that point, provided the surface is not a sphere or
the discs do not cover it. This is the disc intersection in (3.1)(iii). -/
theorem discs_inter_eq_singleton_of_boundaries_meet_once
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {D E : Set S} {u : S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    (hcap : discBd D ∩ discBd E = {u})
    (hDE : ¬ D ⊆ E) (hED : ¬ E ⊆ D)
    (hcase : ¬ IsSphere S ∨ D ∪ E ≠ univ) : D ∩ E = {u} := by
  have hDI := discInt_disjoint_of_boundaries_meet_once hS hD hE hcap hDE hED hcase
  have hcase' : ¬ IsSphere S ∨ E ∪ D ≠ univ := by
    simpa only [union_comm] using hcase
  have hcap' : discBd E ∩ discBd D = {u} := by rw [inter_comm, hcap]
  have hEI := discInt_disjoint_of_boundaries_meet_once hS hE hD hcap' hED hDE hcase'
  apply Subset.antisymm
  · intro x hx
    have hxD : x ∈ discBd D := by
      by_contra hn
      exact Set.disjoint_left.mp hDI ⟨hx.1, hn⟩ hx.2
    have hxE : x ∈ discBd E := by
      by_contra hn
      exact Set.disjoint_left.mp hEI ⟨hx.2, hn⟩ hx.1
    exact hcap ▸ (show x ∈ discBd D ∩ discBd E from ⟨hxD, hxE⟩)
  · intro x hx
    have hxB : x ∈ discBd D ∩ discBd E := hcap.symm ▸ hx
    exact ⟨discBd_subset D hxB.1, discBd_subset E hxB.2⟩

end GraphMinor.GM12
