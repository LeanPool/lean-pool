/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Lines and circles in a smaller ambient space

When XII (3.1), page 245, reads its drawing in the punctured surface,
its edge closures remain lines or circles. Restricting the ambient
space to a set containing an arc does not change that arc as a
topological space. The homeomorphism is the identity on its points.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

private def setHomeomorphInSubspace {S : Type*} [TopologicalSpace S]
    {L C : Set S} (hLC : L ⊆ C) :
    L ≃ₜ ((Subtype.val : C → S) ⁻¹' L) where
  toFun x := ⟨⟨x.val, hLC x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- A line with its two endpoints remains a line in a subspace that
contains the whole line. -/
theorem isLineWithEnds_subtype_preimage {S : Type*} [TopologicalSpace S]
    {L C : Set S} (hLC : L ⊆ C) {v w : C}
    (hL : IsLineWithEnds L v.val w.val) :
    IsLineWithEnds ((Subtype.val : C → S) ⁻¹' L) v w := by
  obtain ⟨f, hf0, hf1⟩ := hL
  refine ⟨f.trans (setHomeomorphInSubspace hLC), ?_, ?_⟩
  · apply Subtype.ext
    exact hf0
  · apply Subtype.ext
    exact hf1

/-- A line and its endpoints are preserved on inclusion from a
subspace into the original surface. -/
theorem isLineWithEnds_subtype_image {S : Type*} [TopologicalSpace S]
    {C : Set S} {L : Set C} {v w : C} (hL : IsLineWithEnds L v w) :
    IsLineWithEnds ((Subtype.val : C → S) '' L) v.val w.val := by
  obtain ⟨f, hf0, hf1⟩ := hL
  refine ⟨f.trans (Topology.IsEmbedding.subtypeVal.homeomorphImage L), ?_, ?_⟩
  · exact congrArg Subtype.val hf0
  · exact congrArg Subtype.val hf1

/-- A circle remains a circle in a subspace containing it. -/
theorem isOArc_subtype_preimage {S : Type*} [TopologicalSpace S]
    {L C : Set S} (hLC : L ⊆ C) (hL : IsOArc L) :
    IsOArc ((Subtype.val : C → S) ⁻¹' L) := by
  obtain ⟨f⟩ := hL
  exact ⟨f.trans (setHomeomorphInSubspace hLC)⟩

/-- A closed disc in a containing subspace has the same boundary,
read through the inclusion. The homeomorphism fixes every point. -/
theorem isClosedDisc_subtype_preimage {S : Type*} [TopologicalSpace S]
    {D C : Set S} (hDC : D ⊆ C) (hD : IsClosedDisc D) :
    IsClosedDisc ((Subtype.val : C → S) ⁻¹' D) ∧
      discBd ((Subtype.val : C → S) ⁻¹' D) =
        (Subtype.val : C → S) ⁻¹' discBd D := by
  obtain ⟨φ⟩ := hD
  let ψ := φ.trans (setHomeomorphInSubspace hDC)
  refine ⟨⟨ψ⟩, ?_⟩
  rw [disc_boundary _ ψ, disc_boundary _ φ]
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨w, hw, Subtype.ext he⟩

/-- Including a closed disc from a subspace into the ambient space
preserves its disc structure and its boundary. -/
theorem isClosedDisc_subtype_image {S : Type*} [TopologicalSpace S]
    {C : Set S} {D : Set C} (hD : IsClosedDisc D) :
    IsClosedDisc ((Subtype.val : C → S) '' D) ∧
      discBd ((Subtype.val : C → S) '' D) =
        (Subtype.val : C → S) '' discBd D := by
  obtain ⟨φ⟩ := hD
  let e := IsEmbedding.subtypeVal.homeomorphImage D
  refine ⟨⟨φ.trans e⟩, ?_⟩
  rw [disc_boundary _ (φ.trans e), disc_boundary _ φ, image_image]
  rfl

/-- Closure in a smaller ambient space is the preimage of ambient
closure when the original set is wholly in the subspace. -/
theorem closure_subtype_preimage {S : Type*} [TopologicalSpace S]
    {L C : Set S} (hLC : L ⊆ C) :
    closure ((Subtype.val : C → S) ⁻¹' L) = (Subtype.val : C → S) ⁻¹' closure L := by
  rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image, Subtype.image_preimage_coe,
    inter_eq_right.mpr hLC]

end GraphMinor.GM12
