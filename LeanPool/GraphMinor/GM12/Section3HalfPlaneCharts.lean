/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Cuffs

/-!
# Reading complex half-plane charts as surface charts

For the punctured surface of XII (3.1), page 245, the remaining local
charts are charts at the prescribed disc boundaries. Circle coordinates
are naturally written in the complex plane. A chart onto the intersection
of an open complex set with the right half-plane gives the half-space
chart required by the definition of a surface.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A complex half-plane chart is a manifold-with-boundary chart.
The coordinate change is the fixed real-linear identification of the
complex plane with the Euclidean plane. -/
theorem isManifoldPoint_of_complex_halfPlane_chart {X : Type*} [TopologicalSpace X]
    {U : Set X} {x : X} (hU : IsOpen U) (hxU : x ∈ U) {O : Set ℂ} (hO : IsOpen O)
    (e : U ≃ₜ (O ∩ halfPlane : Set ℂ)) : IsManifoldPoint x := by
  let V : Set (EuclideanHalfSpace 2) := {v | complexPlane.symm v.val ∈ O}
  have hV : IsOpen V := hO.preimage (complexPlane.symm.continuous.comp continuous_subtype_val)
  let E : (O ∩ halfPlane : Set ℂ) ≃ₜ V := {
    toFun := fun z => ⟨⟨complexPlane z.val, by
      rw [complexPlane_zero]
      exact z.property.2⟩, by
      change complexPlane.symm (complexPlane z.val) ∈ O
      rw [complexPlane.symm_apply_apply]
      exact z.property.1⟩
    invFun := fun v => ⟨complexPlane.symm v.val.val, ⟨v.property, by
      change 0 ≤ (complexPlane.symm v.val.val).re
      rw [← complexPlane_zero, complexPlane.apply_symm_apply]
      exact v.val.property⟩⟩
    left_inv := fun z => Subtype.ext (complexPlane.symm_apply_apply z.val)
    right_inv := fun v => Subtype.ext (Subtype.ext (complexPlane.apply_symm_apply v.val.val))
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      exact complexPlane.continuous.comp continuous_subtype_val
    continuous_invFun := by
      apply Continuous.subtype_mk
      exact complexPlane.symm.continuous.comp (continuous_subtype_val.comp continuous_subtype_val) }
  exact ⟨U, V, hU, hV, hxU, ⟨e.trans E⟩⟩

end GraphMinor.GM12
