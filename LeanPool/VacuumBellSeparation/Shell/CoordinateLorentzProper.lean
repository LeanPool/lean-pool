/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.CoordinatePlaneRotations
public import LeanPool.VacuumBellSeparation.Shell.SpacetimeFrameCoordinates

/-!
# Properness of the actual boost and first plane rotation

The determinants are computed in the literal time-first basis of the
original spacetime carrier. No path-connectedness or orientation
assumption is used to identify these parameter maps as proper.
-/

@[expose] public section

namespace VacuumBellSeparation

theorem boost_to_spacetimeFrameMatrix (η : ℝ) :
    LinearMap.toMatrix spacetimeFrameBasis spacetimeFrameBasis (boost η).toLinearEquiv.toLinearMap =
      ![![Real.cosh η, Real.sinh η, 0, 0],
        ![Real.sinh η, Real.cosh η, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1]] := by
  have hb1 : spacetimeFrameBasis 1 = spacetimeAxis 0 := spacetimeFrameBasis_succ 0
  have hb2 : spacetimeFrameBasis 2 = spacetimeAxis 1 := spacetimeFrameBasis_succ 1
  have hb3 : spacetimeFrameBasis 3 = spacetimeAxis 2 := spacetimeFrameBasis_succ 2
  have hc1 (x : Spacetime) : spacetimeFrameCoordinates x 1 = x.2 0 :=
    spacetimeFrameCoordinates_succ x 0
  have hc2 (x : Spacetime) : spacetimeFrameCoordinates x 2 = x.2 1 :=
    spacetimeFrameCoordinates_succ x 1
  have hc3 (x : Spacetime) : spacetimeFrameCoordinates x 3 = x.2 2 :=
    spacetimeFrameCoordinates_succ x 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, spacetimeFrameBasis_repr,
      spacetimeFrameBasis_zero, hb1, hb2, hb3, spacetimeFrameCoordinates_zero, hc1, hc2, hc3,
      spacetimeAxis, boost_apply, boostCLM_apply, e₁, EuclideanSpace.inner_single_left]

theorem spatialPlaneRotation_to_spacetimeFrameMatrix (θ : ℝ) :
    LinearMap.toMatrix spacetimeFrameBasis spacetimeFrameBasis
      (spatialRotation (spatialPlaneRotation θ)).toLinearEquiv.toLinearMap =
      ![![1, 0, 0, 0], ![0, Real.cos θ, -Real.sin θ, 0],
        ![0, Real.sin θ, Real.cos θ, 0], ![0, 0, 0, 1]] := by
  have hb1 : spacetimeFrameBasis 1 = spacetimeAxis 0 := spacetimeFrameBasis_succ 0
  have hb2 : spacetimeFrameBasis 2 = spacetimeAxis 1 := spacetimeFrameBasis_succ 1
  have hb3 : spacetimeFrameBasis 3 = spacetimeAxis 2 := spacetimeFrameBasis_succ 2
  have hc1 (x : Spacetime) : spacetimeFrameCoordinates x 1 = x.2 0 :=
    spacetimeFrameCoordinates_succ x 0
  have hc2 (x : Spacetime) : spacetimeFrameCoordinates x 2 = x.2 1 :=
    spacetimeFrameCoordinates_succ x 1
  have hc3 (x : Spacetime) : spacetimeFrameCoordinates x 3 = x.2 2 :=
    spacetimeFrameCoordinates_succ x 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LinearMap.toMatrix_apply, spacetimeFrameBasis_repr,
      spacetimeFrameBasis_zero, hb1, hb2, hb3, spacetimeFrameCoordinates_zero, hc1, hc2, hc3,
      spacetimeAxis, spatialRotation_apply, spatialPlaneRotation_apply]

theorem isProperLorentzMap_boost (η : ℝ) : IsProperLorentzMap (boost η) :=
  ⟨isLorentzMap_boost η, det_boost η⟩

theorem isProperLorentzMap_spatialPlaneRotation (θ : ℝ) :
    IsProperLorentzMap (spatialRotation (spatialPlaneRotation θ)) := by
  refine ⟨isLorentzMap_spatialRotation _, ?_⟩
  rw [← LinearMap.det_toMatrix spacetimeFrameBasis, spatialPlaneRotation_to_spacetimeFrameMatrix]
  change Matrix.det !![1, 0, 0, 0; 0, Real.cos θ, -Real.sin θ, 0;
    0, Real.sin θ, Real.cos θ, 0; 0, 0, 0, 1] = 1
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.det_unique, Matrix.submatrix_apply]
  norm_num
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem isOrthochronousMap_boost (η : ℝ) : IsOrthochronousMap (boost η) := by
  simpa only [IsOrthochronousMap, boost_apply, boostCLM_apply,
    mul_one, inner_zero_right, mul_zero, add_zero] using Real.cosh_pos η

theorem isOrthochronousMap_spatialRotation
    (R : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    IsOrthochronousMap (spatialRotation R) := by
  change (0 : ℝ) < 1
  norm_num

end VacuumBellSeparation
