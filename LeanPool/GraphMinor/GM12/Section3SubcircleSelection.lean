/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SolidPlanarity
public import LeanPool.GraphMinor.GM12.Section3PlanarityMaps
import LeanPool.GraphMinor.GM12.Section3SolidEmbedding

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Selecting circles in a solid set which is not near-planar

The Section 8 argument of VII used in XII (3.1), page 245, begins
with nonplanar circles. Apply the planar criterion in a cap to obtain
one even when the solid set fills the original surface. If every such
circle is near-planar, choose one surrounding a cuff. The uniform-cuff
criterion forces another circle which is not planar in that cap.
It either is not near-planar or surrounds a different cuff.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- A solid set which is not near-planar contains a nonplanar circle
when the connected surface has a cuff. The proof uses a cap to make
the image a proper subset before applying VII (5.1). -/
theorem exists_nonplanar_subcircle_with_cuff
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hCuff : (cuffs S).Nonempty)
    {X : Set S} (hX : IsSolid X) (hnot : ¬ GM07.IsNearPlanar X) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ X ∧ ¬ IsPlanar F := by
  obtain ⟨C, hC⟩ := hCuff
  obtain ⟨T, tT, j, D, hcap⟩ := exists_cappedCuff hS hC
  have hconn := cappedCuff_connectedSpace hcap
  have hsolid := isSolid_image_isClosedEmbedding (cappedCuff_isClosedEmbedding hS hcap) hX
  have hproper : j '' X ≠ univ := by
    intro heq
    apply cappedCuff_range_ne_univ hcap
    apply eq_univ_of_univ_subset
    rw [← heq]
    rintro y ⟨x, _, rfl⟩
    exact mem_range_self x
  have hnotplan : ¬ IsPlanar (j '' X) := by
    intro hp
    exact hnot (Or.inr ⟨C, hC, isPlanarInCappedCuff_of_one_cap hS hcap hp⟩)
  obtain ⟨F, hF, hFX, hnotF⟩ := exists_nonplanar_subcircle_of_not_planar
    hcap.isSurface hconn hsolid hproper hnotplan
  have hFrange : F ⊆ range j := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := hFX hy
    exact mem_range_self x
  have hpreF := isOArc_preimage_isEmbedding hcap.isEmbedding hF hFrange
  have hpreX : j ⁻¹' F ⊆ X := by
    intro x hx
    obtain ⟨y, hy, he⟩ := hFX hx
    exact hcap.isEmbedding.injective he ▸ hy
  refine ⟨j ⁻¹' F, hpreF, hpreX, ?_⟩
  intro hp
  have himage := isPlanar_image_isEmbedding hcap.isEmbedding hp
  rw [image_preimage_eq_of_subset hFrange] at himage
  exact hnotF himage

/-- The first selection step of VII Section 8: a solid set which is
not near-planar contains either a circle which is not near-planar or
two circles surrounding distinct cuffs. Their intersection patterns
are handled separately when constructing the schismatic shapes. -/
theorem exists_non_nearplanar_circle_or_distinct_surrounding_circles
    {S : Type u} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hCuff : (cuffs S).Nonempty)
    {X : Set S} (hX : IsSolid X) (hnot : ¬ GM07.IsNearPlanar X) :
    (∃ F : Set S, IsOArc F ∧ F ⊆ X ∧ ¬ GM07.IsNearPlanar F) ∨
      ∃ F A C C' : Set S, IsOArc F ∧ IsOArc A ∧ F ⊆ X ∧ A ⊆ X ∧
        IsCuff C ∧ IsCuff C' ∧ C ≠ C' ∧ GM07.SurroundsCuff F C ∧ GM07.SurroundsCuff A C' := by
  classical
  obtain ⟨F, hF, hFX, hnotF⟩ := exists_nonplanar_subcircle_with_cuff hS hCuff hX hnot
  by_cases hnearF : GM07.IsNearPlanar F
  · rcases hnearF with hpF | ⟨C, hC, hpFC⟩
    · exact False.elim (hnotF hpF)
    · obtain ⟨T, tT, j, D, hcap⟩ := exists_cappedCuff hS hC
      have hex : ∃ A : Set S, IsOArc A ∧ A ⊆ X ∧ ¬ GM07.IsPlanarInCappedCuff C A := by
        by_contra hn
        apply hnot
        right
        refine ⟨C, hC, planarInCappedCuff_of_all_subcircles hS hcap hX ?_⟩
        intro A hA hAX
        by_contra hnotA
        exact hn ⟨A, hA, hAX, hnotA⟩
      obtain ⟨A, hA, hAX, hnotAC⟩ := hex
      by_cases hnearA : GM07.IsNearPlanar A
      · rcases hnearA with hpA | ⟨C', hC', hpAC'⟩
        · exact False.elim (hnotAC (isPlanarInCappedCuff_of_isPlanar hS hC hpA))
        · have hnotA : ¬ IsPlanar A := fun hpA =>
            hnotAC (isPlanarInCappedCuff_of_isPlanar hS hC hpA)
          have hCC' : C ≠ C' := by
            intro he
            apply hnotAC
            rw [he]
            exact hpAC'
          exact Or.inr ⟨F, A, C, C', hF, hA, hFX, hAX, hC, hC', hCC',
            ⟨hC, hpFC, hnotF⟩, ⟨hC', hpAC', hnotA⟩⟩
      · exact Or.inl ⟨A, hA, hAX, hnearA⟩
  · exact Or.inl ⟨F, hF, hFX, hnearF⟩

end GraphMinor.GM12
