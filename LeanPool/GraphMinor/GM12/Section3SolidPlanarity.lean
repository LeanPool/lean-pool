/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
public import LeanPool.GraphMinor.GM12.Section3CapTopology
public import LeanPool.GraphMinor.GM12.Section3CapComparison
import LeanPool.GraphMinor.GM12.Section3SolidEmbedding
import LeanPool.GraphMinor.Surface.DiscsInSurface

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Planar criteria for the schismatic argument

The unnumbered Section 8 argument of VII used in XII (3.1), page 245,
uses VII (5.1) both in the original surface and in a cap. A planar
circle is null-homotopic because it lies in a disc. In a cap, solidity
passes through the closed embedding and the image is a proper subset.
Thus circles planar after one fixed cuff is filled make the whole
solid set planar after that same filling.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

universe u

/-- VII (5.1) makes a proper solid set planar if all its circles are
planar. The discs containing those circles contract their parametrizations. -/
theorem planar_of_all_subcircles_planar
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S) (hconn : ConnectedSpace S)
    {X : Set S} (hX : IsSolid X) (hproper : X ≠ univ)
    (hcircles : ∀ F : Set S, IsOArc F → F ⊆ X → IsPlanar F) : IsPlanar X := by
  apply (GraphMinor.GM07.gm07_theorem_5_1 S hS hconn X hX hproper).mpr
  intro F hF hFX
  obtain ⟨D, hD, hFD⟩ := hcircles F hF hFX
  exact isNullHomotopicOArcIn_of_subset_disc hF (subset_univ D) hD hFD

/-- A proper solid nonplanar set contains a nonplanar circle, by
VII (5.1). This is the first circle-selection step of Section 8. -/
theorem exists_nonplanar_subcircle_of_not_planar
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S) (hconn : ConnectedSpace S)
    {X : Set S} (hX : IsSolid X) (hproper : X ≠ univ) (hnot : ¬ IsPlanar X) :
    ∃ F : Set S, IsOArc F ∧ F ⊆ X ∧ ¬ IsPlanar F := by
  by_contra hn
  apply hnot
  apply planar_of_all_subcircles_planar hS hconn hX hproper
  intro F hF hFX
  by_contra hnotF
  exact hn ⟨F, hF, hFX, hnotF⟩

/-- If every circle of a solid set is planar after filling one fixed
cuff, then the whole set is planar after filling that cuff. This applies
VII (5.1) in the actual cap, with all its hypotheses proved. -/
theorem planarInCappedCuff_of_all_subcircles
    {S T : Type u} [TopologicalSpace S] [TopologicalSpace T] [ConnectedSpace S]
    (hS : IsSurface S) {C X : Set S} {j : S → T} {D : Set T}
    (hcap : GM07.IsCappedCuff C T j D) (hX : IsSolid X)
    (hcircles : ∀ F : Set S, IsOArc F → F ⊆ X → GM07.IsPlanarInCappedCuff C F) :
    GM07.IsPlanarInCappedCuff C X := by
  have hconn : ConnectedSpace T := cappedCuff_connectedSpace hcap
  have hjclosed := cappedCuff_isClosedEmbedding hS hcap
  have hsolid : IsSolid (j '' X) := isSolid_image_isClosedEmbedding hjclosed hX
  have hproper : j '' X ≠ univ := by
    intro heq
    apply cappedCuff_range_ne_univ hcap
    apply eq_univ_of_univ_subset
    rw [← heq]
    rintro y ⟨x, _, rfl⟩
    exact mem_range_self x
  have hplan : IsPlanar (j '' X) := by
    apply planar_of_all_subcircles_planar hcap.isSurface hconn hsolid hproper
    intro F hF hFX
    have hFrange : F ⊆ range j := by
      intro y hy
      obtain ⟨x, _, rfl⟩ := hFX hy
      exact mem_range_self x
    have hpreF := isOArc_preimage_isEmbedding hcap.isEmbedding hF hFrange
    have hpreX : j ⁻¹' F ⊆ X := by
      intro x hx
      obtain ⟨y, hy, he⟩ := hFX hx
      exact hcap.isEmbedding.injective he ▸ hy
    have hp := (hcircles (j ⁻¹' F) hpreF hpreX).2.2 T j D hcap
    rw [image_preimage_eq_of_subset hFrange] at hp
    exact hp
  exact isPlanarInCappedCuff_of_one_cap hS hcap hplan

end GraphMinor.GM12
