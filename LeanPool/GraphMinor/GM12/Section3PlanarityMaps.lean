/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CapTopology
public import LeanPool.GraphMinor.GM12.Section3CapComparison
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Planarity under inclusion and embeddings

For the Section 8 argument of VII used in XII (3.1), page 245,
planarity and near-planarity pass to subsets. Embeddings carry a
containing disc to a containing disc. In particular, a planar set is
planar after any chosen cuff is filled.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- A subset of a planar set lies in the same containing disc. -/
theorem isPlanar_mono {S : Type*} [TopologicalSpace S] {X Y : Set S}
    (hXY : X ⊆ Y) (hY : IsPlanar Y) : IsPlanar X := by
  obtain ⟨D, hD, hYD⟩ := hY
  exact ⟨D, hD, hXY.trans hYD⟩

/-- An embedding carries a planar set into the image of its containing disc. -/
theorem isPlanar_image_isEmbedding
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {X : Set S} (hX : IsPlanar X) : IsPlanar (j '' X) := by
  obtain ⟨D, hD, hXD⟩ := hX
  obtain ⟨φ⟩ := hD
  exact ⟨j '' D, ⟨φ.trans (hj.homeomorphImage D)⟩, image_mono hXD⟩

/-- Planarity after filling a cuff passes to subsets in every cap. -/
theorem isPlanarInCappedCuff_mono
    {S : Type u} [TopologicalSpace S] {C X Y : Set S}
    (hXY : X ⊆ Y) (hY : GM07.IsPlanarInCappedCuff C Y) : GM07.IsPlanarInCappedCuff C X := by
  refine ⟨hY.1, ?_, ?_⟩
  · obtain ⟨T, tT, j, D, hcap, hp⟩ := hY.2.1
    exact ⟨T, tT, j, D, hcap, isPlanar_mono (image_mono hXY) hp⟩
  · intro T _ j D hcap
    exact isPlanar_mono (image_mono hXY) (hY.2.2 T j D hcap)

/-- Near-planarity passes to subsets, retaining the same containing
disc or the same cuff. -/
theorem isNearPlanar_mono
    {S : Type u} [TopologicalSpace S] {X Y : Set S}
    (hXY : X ⊆ Y) (hY : GM07.IsNearPlanar Y) : GM07.IsNearPlanar X := by
  rcases hY with hp | ⟨C, hC, hp⟩
  · exact Or.inl (isPlanar_mono hXY hp)
  · exact Or.inr ⟨C, hC, isPlanarInCappedCuff_mono hXY hp⟩

/-- A planar set remains planar after any existing cuff is filled. -/
theorem isPlanarInCappedCuff_of_isPlanar
    {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {C X : Set S} (hC : IsCuff C) (hX : IsPlanar X) : GM07.IsPlanarInCappedCuff C X := by
  obtain ⟨T, tT, j, D, hcap⟩ := exists_cappedCuff hS hC
  exact isPlanarInCappedCuff_of_one_cap hS hcap (isPlanar_image_isEmbedding hcap.isEmbedding hX)

end GraphMinor.GM12
