/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CompactTraceNorm
public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryDensityExpectation

/-! # Actual nuclear trace and compactness under Hilbert-space unitaries -/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem conjStarAlgEquiv_abs (e : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    e.conjStarAlgEquiv (CFC.abs A) = CFC.abs (e.conjStarAlgEquiv A) := by
  rw [CFC.abs, conjStarAlgEquiv_sqrt e (star_mul_self_nonneg A), map_mul, map_star]
  rfl

theorem operatorTraceNorm_conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    operatorTraceNorm (e.conjStarAlgEquiv A) = operatorTraceNorm A := by
  rw [operatorTraceNorm, ← conjStarAlgEquiv_abs, positiveTrace_conjStarAlgEquiv e
    (CFC.abs_nonneg A)]
  rfl

theorem norm_conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) :
    ‖e.conjStarAlgEquiv A‖ = ‖A‖ := StarAlgEquiv.norm_map e.conjStarAlgEquiv A

theorem isSelfAdjoint_conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E}
    (hA : IsSelfAdjoint A) : IsSelfAdjoint (e.conjStarAlgEquiv A) := by
  change star (e.conjStarAlgEquiv A) = e.conjStarAlgEquiv A
  rw [← map_star, hA.star_eq]

theorem isCompactOperator_conjStarAlgEquiv (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E}
    (hA : IsCompactOperator A) : IsCompactOperator (e.conjStarAlgEquiv A) := by
  have h := (hA.comp_clm e.symm.toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
    e.toContinuousLinearEquiv.toContinuousLinearMap
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply, coe_comp] using h

end VacuumBellSeparation.Gaussian
