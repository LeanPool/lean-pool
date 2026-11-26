/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
public import LeanPool.GraphMinor.GM12.Section3PuncturedSurface
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Feasibility discs in the punctured surface

In XII (3.1), page 245, each topological feasibility disc meets the
deleted discs only at its prescribed boundary vertices. Consequently
it lies in Sigma-star. A closed disc in a surface can meet the surface
boundary only on its own boundary. Thus the prescribed vertices lie
on the feasibility disc boundary, where a finite star can be drawn.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A closed disc in a surface meets the surface boundary only on its
own boundary, since each point of its interior is an interior point
of the surface. -/
theorem disc_inter_surface_boundary_subset_discBd
    {S : Type*} [TopologicalSpace S] (hS : IsSurface S)
    {D : Set S} (hD : IsClosedDisc D) : D ∩ bd S ⊆ discBd D := by
  intro x hx
  by_contra hn
  exact hx.2 (isInteriorPoint_of_mem_discInt hS.2.2 hD ⟨hx.1, hn⟩)

/-- A feasibility disc remains in Sigma-star when all its contacts
with the deleted discs belong to their retained boundaries. -/
theorem feasibility_disc_subset_discComplement
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {D Z : Set S} (hcontact : D ∩ ⋃ i, Δ i = Z)
    (hZ : Z ⊆ ⋃ i, discBd (Δ i)) : D ⊆ discComplement Δ := by
  intro x hxD
  by_cases hx : x ∈ ⋃ i, Δ i
  · have hxZ : x ∈ Z := hcontact ▸ ⟨hxD, hx⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hZ hxZ)
    exact disc_boundary_subset_discComplement hS Δ hΔ hdisj i hxi
  · exact subset_closure hx

/-- The prescribed contacts of a feasibility disc lie on its own
boundary, as needed for the star in XII (3.1). -/
theorem feasibility_contacts_subset_discBd
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {D Z : Set S} (hD : IsClosedDisc D) (hcontact : D ∩ ⋃ i, Δ i = Z)
    (hZ : Z ⊆ ⋃ i, discBd (Δ i)) : Z ⊆ discBd D := by
  have hDC := feasibility_disc_subset_discComplement hS Δ hΔ hdisj hcontact hZ
  have hdisc := isClosedDisc_subtype_preimage hDC hD
  intro x hxZ
  have hxD : x ∈ D := (hcontact.symm ▸ hxZ).1
  let y : discComplement Δ := ⟨x, hDC hxD⟩
  have hyB : y ∈ bd (discComplement Δ) := by
    rw [discComplement_boundary_eq hS Δ hΔ]
    exact hZ hxZ
  have hyD : y ∈ (Subtype.val : discComplement Δ → S) ⁻¹' D := hxD
  have hy := disc_inter_surface_boundary_subset_discBd
    (discComplement_isSurface hS Δ hΔ hdisj) hdisc.1 ⟨hyD, hyB⟩
  rw [hdisc.2] at hy
  exact hy

end GraphMinor.GM12
