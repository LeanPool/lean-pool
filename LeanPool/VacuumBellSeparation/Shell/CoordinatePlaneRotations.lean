/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.LorentzMap

/-!
# Actual spatial coordinate-plane rotations

The first two spatial coordinates are rotated by the ordinary real
cosine/sine matrix, leaving the third fixed. Exact inverse and norm
identities construct an isometry. Coordinate permutations transport it
to the other spatial planes used by the contour parameter chart.
-/

@[expose] public section

namespace VacuumBellSeparation

/-- Linear map for the spatial plane rotation linear, of type `EuclideanSpace ℝ (Fin 3) →ₗ[ℝ]
EuclideanSpace ℝ (Fin 3) where toFun x`. -/
noncomputable def spatialPlaneRotationLinear (θ : ℝ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := WithLp.toLp 2 ![Real.cos θ * x 0 - Real.sin θ * x 1,
    Real.sin θ * x 0 + Real.cos θ * x 1, x 2]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem spatialPlaneRotationLinear_norm_sq (θ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    ‖spatialPlaneRotationLinear θ x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_three, spatialPlaneRotationLinear, LinearMap.coe_mk,
    AddHom.coe_mk, PiLp.toLp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two]
  change (Real.cos θ * x 0 - Real.sin θ * x 1) ^ 2 +
    (Real.sin θ * x 0 + Real.cos θ * x 1) ^ 2 + x 2 ^ 2 =
      x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
  calc
    _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * (x 0 ^ 2 + x 1 ^ 2) + x 2 ^ 2 := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]

theorem spatialPlaneRotationLinear_inverse (θ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialPlaneRotationLinear (-θ) (spatialPlaneRotationLinear θ x) = x := by
  have h0 : Real.cos θ * (Real.cos θ * x 0 - Real.sin θ * x 1) +
      Real.sin θ * (Real.sin θ * x 0 + Real.cos θ * x 1) = x 0 := by
    calc
      _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * x 0 := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
  have h1 : -Real.sin θ * (Real.cos θ * x 0 - Real.sin θ * x 1) +
      Real.cos θ * (Real.sin θ * x 0 + Real.cos θ * x 1) = x 1 := by
    calc
      _ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) * x 1 := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq, one_mul]
  ext i
  fin_cases i
  · simpa [spatialPlaneRotationLinear, Real.cos_neg, Real.sin_neg] using h0
  · simpa [spatialPlaneRotationLinear, Real.cos_neg, Real.sin_neg] using h1
  · rfl

/-- Linear isometric rotation of the designated plane in three-dimensional space. -/
noncomputable def spatialPlaneRotation (θ : ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearEquiv :=
    { spatialPlaneRotationLinear θ with
      invFun := spatialPlaneRotationLinear (-θ)
      left_inv := spatialPlaneRotationLinear_inverse θ
      right_inv := fun x => by
        change spatialPlaneRotationLinear θ (spatialPlaneRotationLinear (-θ) x) = x
        simpa only [neg_neg] using spatialPlaneRotationLinear_inverse (-θ) x }
  norm_map' x := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (spatialPlaneRotationLinear_norm_sq θ x)

theorem spatialPlaneRotation_apply (θ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialPlaneRotation θ x = WithLp.toLp 2
      ![Real.cos θ * x 0 - Real.sin θ * x 1,
        Real.sin θ * x 0 + Real.cos θ * x 1, x 2] := rfl

theorem spatialPlaneRotation_zero : spatialPlaneRotation 0 = LinearIsometryEquiv.refl ℝ _ := by
  ext x i
  fin_cases i <;> simp [spatialPlaneRotation_apply]

/-- Spatial coordinate permutation obtained from `LinearIsometryEquiv.piLpCongrLeft`. -/
noncomputable def spatialCoordinatePermutation (σ : Equiv.Perm (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

/-- Linear isometry equivalence for the spatial plane rotation13, of type `EuclideanSpace ℝ (Fin 3)
≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def spatialPlaneRotation13 (θ : ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (spatialCoordinatePermutation (Equiv.swap 1 2)).trans
    ((spatialPlaneRotation θ).trans (spatialCoordinatePermutation (Equiv.swap 1 2)))

/-- Linear isometry equivalence for the spatial plane rotation23, of type `EuclideanSpace ℝ (Fin 3)
≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def spatialPlaneRotation23 (θ : ℝ) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (spatialCoordinatePermutation (Equiv.swap 0 1)).trans
    ((spatialPlaneRotation13 θ).trans (spatialCoordinatePermutation (Equiv.swap 0 1)))

theorem spatialPlaneRotation13_apply (θ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialPlaneRotation13 θ x = WithLp.toLp 2
      ![Real.cos θ * x 0 - Real.sin θ * x 2, x 1,
        Real.sin θ * x 0 + Real.cos θ * x 2] := by
  ext i
  fin_cases i <;> simp [spatialPlaneRotation13, spatialCoordinatePermutation,
    LinearIsometryEquiv.piLpCongrLeft_apply, spatialPlaneRotation_apply,
    Equiv.piCongrLeft', Equiv.swap_apply_def]

theorem spatialPlaneRotation23_apply (θ : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    spatialPlaneRotation23 θ x = WithLp.toLp 2
      ![x 0, Real.cos θ * x 1 - Real.sin θ * x 2,
        Real.sin θ * x 1 + Real.cos θ * x 2] := by
  ext i
  fin_cases i <;> simp [spatialPlaneRotation23, spatialCoordinatePermutation,
    LinearIsometryEquiv.piLpCongrLeft_apply, spatialPlaneRotation13_apply,
    Equiv.piCongrLeft', Equiv.swap_apply_def]

end VacuumBellSeparation
