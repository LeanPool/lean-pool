/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Solid sets under closed embeddings

The Section 8 argument of VII used in XII (3.1), page 245, applies
the planar criterion inside a capped surface. A closed embedding
preserves a solid set: closedness passes through the closed map, and
open neighbourhoods pull back to the original space. Arc connections
map to arc connections by the embedding.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- An embedding preserves arc-connectedness by mapping each line
homeomorphically onto its image. -/
theorem isArcConnected_image_isEmbedding
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {X : Set S} (hX : IsArcConnected X) :
    IsArcConnected (j '' X) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
  have hab' : a ≠ b := fun he => hab (congrArg j he)
  obtain ⟨L, hLX, φ, hφ0, hφ1⟩ := hX a ha b hb hab'
  refine ⟨j '' L, image_mono hLX, φ.trans (hj.homeomorphImage L), ?_, ?_⟩
  · exact congrArg j hφ0
  · exact congrArg j hφ1

/-- A circle contained in an embedding's range pulls back to a
circle in the source. The map is the inverse of inclusion on that set. -/
theorem isOArc_preimage_isEmbedding
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {j : S → T} (hj : IsEmbedding j) {F : Set T}
    (hF : IsOArc F) (hFrange : F ⊆ range j) : IsOArc (j ⁻¹' F) := by
  let e : (j ⁻¹' F) ≃ₜ F := (hj.homeomorphImage (j ⁻¹' F)).trans
    (Homeomorph.setCongr (image_preimage_eq_of_subset hFrange))
  obtain ⟨φ⟩ := hF
  exact ⟨φ.trans e.symm⟩

/-- A closed embedding preserves the solid sets used in VII's alpha
parameter. Every local arc-connected neighbourhood is the pullback of
an ambient open neighbourhood. -/
theorem isSolid_image_isClosedEmbedding
    {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
    {j : S → T} (hj : IsClosedEmbedding j) {X : Set S} (hX : IsSolid X) :
    IsSolid (j '' X) := by
  refine ⟨?_, hj.isClosedMap X hX.2⟩
  rintro _ ⟨x, hxX, rfl⟩ O hO hxO
  obtain ⟨A, hAsub, hxA, hA, hArc⟩ := hX.1 x hxX (j ⁻¹' O)
    (hO.preimage hj.continuous) hxO
  obtain ⟨B, hB, hpre⟩ := hj.isEmbedding.isInducing.isOpen_iff.mp hA
  have hxB : j x ∈ B := by
    change x ∈ j ⁻¹' B
    rw [hpre]
    exact hxA
  refine ⟨B ∩ O, inter_subset_right, ⟨hxB, hxO⟩, hB.inter hO, ?_⟩
  have himage : j '' (X ∩ A) = j '' X ∩ (B ∩ O) := by
    ext y
    constructor
    · rintro ⟨z, ⟨hzX, hzA⟩, rfl⟩
      have hzB : j z ∈ B := by
        change z ∈ j ⁻¹' B
        rw [hpre]
        exact hzA
      exact ⟨mem_image_of_mem j hzX, hzB, hAsub hzA⟩
    · rintro ⟨⟨z, hzX, rfl⟩, hzB, hzO⟩
      have hzA : z ∈ A := by
        rw [← hpre]
        exact hzB
      exact ⟨z, ⟨hzX, hzA⟩, rfl⟩
  rw [← himage]
  exact isArcConnected_image_isEmbedding hj.isEmbedding hArc

end GraphMinor.GM12
