/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Gluing
import Mathlib.Topology.LocalAtTarget

/-!
# Restricting a chart to the punctured surface

In XII (3.1), page 245, collar coordinates identify the remaining
surface with a local part of the circle exterior. This lemma transfers
a manifold chart through that local identification.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- An open coordinate map transfers a local surface model to a
subspace whenever membership agrees in those coordinates. -/
theorem isManifoldPoint_of_open_coordinate_model
    {X S : Type*} [TopologicalSpace X] [TopologicalSpace S]
    {M Y : Set X} {C : Set S} (hM : IsOpen M)
    {e : M → S} (he : IsOpenEmbedding e)
    (hmem : ∀ z : M, e z ∈ C ↔ z.val ∈ Y)
    {z : M} (hzY : z.val ∈ Y) (hz : IsManifoldPoint (⟨z.val, hzY⟩ : Y)) :
    IsManifoldPoint (⟨e z, (hmem z).mpr hzY⟩ : C) := by
  let A : Set Y := Subtype.val ⁻¹' M
  have hA : IsOpen A := hM.preimage continuous_subtype_val
  let F : (e ⁻¹' C) ≃ₜ A := {
    toFun := fun w => ⟨⟨w.val.val, (hmem w.val).mp w.property⟩, w.val.property⟩
    invFun := fun w => ⟨⟨w.val.val, w.property⟩, (hmem _).mpr w.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_subtype_val }
  let w : e ⁻¹' C := ⟨z, (hmem z).mpr hzY⟩
  have hwA : IsManifoldPoint (F w) :=
    (isManifoldPoint_iff_of_isOpenEmbedding hA.isOpenEmbedding_subtypeVal).mp hz
  have hw : IsManifoldPoint w :=
    (isManifoldPoint_iff_of_isOpenEmbedding F.isOpenEmbedding).mp hwA
  exact isManifoldPoint_of_isOpenEmbedding (he.restrictPreimage C) hw

end GraphMinor.GM12
