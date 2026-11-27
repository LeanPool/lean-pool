/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioOperator
public import LeanPool.VacuumBellSeparation.FreeField.UnitaryPartialTransport

/-!
# Actual graphs and scalar regularizer changes

Graph equalities retain the complete partial-operator domain. A nonzero
real rescaling of numerator and denominator does not alter a bounded ratio.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace E] in
theorem boundedRatio_mem_graph (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (x y : E) :
    (x, y) ∈ (boundedRatio A B hA).graph ↔ ∃ z, A z = x ∧ B z = y := by
  rw [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨w, hw, hv⟩
    obtain ⟨z, hz, hBz⟩ := boundedRatio_representation A B hA w
    exact ⟨z, hz.trans hw, hBz.trans hv⟩
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨⟨A z, ⟨z, rfl⟩⟩, rfl, boundedRatio_apply_range A B hA z⟩

omit [CompleteSpace E] in
theorem boundedRatio_real_smul (A B : E →L[ℂ] E) (hA : Function.Injective A)
    (a : ℝ) (ha : a ≠ 0) (hAa : Function.Injective (a • A)) :
    boundedRatio (a • A) (a • B) hAa = boundedRatio A B hA := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rcases p with ⟨x, y⟩
  rw [boundedRatio_mem_graph, boundedRatio_mem_graph]
  constructor
  · rintro ⟨z, hz, hv⟩
    refine ⟨a • z, ?_, ?_⟩
    · simpa only [map_smul_of_tower, smul_apply] using hz
    · simpa only [map_smul_of_tower, smul_apply] using hv
  · rintro ⟨z, rfl, rfl⟩
    refine ⟨a⁻¹ • z, ?_, ?_⟩ <;>
      simp only [smul_apply, map_smul_of_tower, smul_smul, mul_inv_cancel₀ ha, one_smul]

omit [CompleteSpace E] [CompleteSpace F] in
theorem unitaryPartialTransport_mem_graph (V : E ≃ₗᵢ[ℂ] F) (T : E →ₗ.[ℂ] E)
    (x y : F) :
    (x, y) ∈ (unitaryPartialTransport V T).graph ↔ (V.symm x, V.symm y) ∈ T.graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨w, hw, hv⟩
    refine ⟨⟨V.symm w, w.property⟩, congrArg V.symm hw, ?_⟩
    simpa only [unitaryPartialTransport_apply, LinearIsometryEquiv.symm_apply_apply] using
      congrArg V.symm hv
  · rintro ⟨w, hw, hv⟩
    have hx : V.symm x ∈ T.domain := by
      change (w : E) = V.symm x at hw
      rw [← hw]
      exact w.property
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    have he : (⟨V.symm x, hx⟩ : T.domain) = w := Subtype.ext hw.symm
    rw [unitaryPartialTransport_apply, he, hv, LinearIsometryEquiv.apply_symm_apply]

end VacuumBellSeparation
