/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SurroundingDisc
public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

/-!
# Boundary linkage from XII (3.1)(v)

Condition (v) of XII (3.1), page 245, bounds the vertex count on a
circle enclosing one prescribed disc. A circle surrounding a cuff in
VII bounds precisely such a disc. The drawing and its vertex counts
are unchanged by inclusion into the original surface, so condition
(v) gives boundary linkage of the drawing in Sigma-star.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Condition (v) of XII (3.1), page 245, implies boundary linkage in
VII's exact sense for the actual drawing in Sigma-star. -/
theorem drawingInDiscComplement_isBoundaryLinked
    {S : Type*} {ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Γ : Drawing S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
    (hbound : ∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
      ∀ D : Set S, IsClosedDisc D → discBd D = F →
      ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
        (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard) :
    GM07.IsBoundaryLinked (drawingInSubspace Γ (discComplement Δ)
      (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)) := by
  let C := discComplement Δ
  let hUC := drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid
  let G := drawingInSubspace Γ C hUC
  refine ⟨drawingInDiscComplement_isProper hS Γ Δ hΔ hdisj havoid, ?_⟩
  intro K hK F hn hF hs
  rw [discComplement_cuffs_eq hS Δ hΔ hdisj] at hK
  obtain ⟨i, rfl⟩ := hK
  obtain ⟨D, hD, hbd, hone⟩ :=
    surrounding_bounds_disc_including_exactly_one hS Δ hΔ hdisj i hF hs
  have hnorm := drawingInSubspace_isNormal_image Γ C hUC hn
  have hFo : IsOArc ((Subtype.val : C → S) '' F) := by
    obtain ⟨φ⟩ := hF
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage F)⟩
  have hcount := hbound _ hnorm hFo (by rintro x ⟨y, _, rfl⟩; exact y.property)
    D hD hbd i hone
  have hbimage : (Subtype.val : C → S) '' (Subtype.val ⁻¹' discBd (Δ i)) = discBd (Δ i) := by
    rw [Subtype.image_preimage_coe]
    exact inter_eq_right.mpr (disc_boundary_subset_discComplement hS Δ hΔ hdisj i)
  have hleft := drawingInSubspace_image_vertices_inter Γ C hUC (Subtype.val ⁻¹' discBd (Δ i))
  rw [hbimage] at hleft
  have hright := drawingInSubspace_image_vertices_inter Γ C hUC F
  rw [← hleft, ← hright, ncard_image_of_injective _ Subtype.val_injective,
    ncard_image_of_injective _ Subtype.val_injective] at hcount
  exact hcount

end GraphMinor.GM12
