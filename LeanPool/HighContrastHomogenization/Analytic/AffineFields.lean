/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.CenteringInvariance
public import LeanPool.HighContrastHomogenization.Analytic.DirichletDomain

/-!
# High-contrast homogenization: Analytic.AffineFields

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fields in the symmetric affine normalization

The symmetric square-root change of variables sends physical gradients and
skew-centered fluxes to the two fields used by the deterministic comparison.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

variable {d : ℕ}

/-- The square-root map carries a gradient difference to the difference of
the transformed gradients. -/
theorem matSqrt_gradient_difference_eq (S : Mat d) (F G : Vec d) :
    matVecMul (matSqrt S) F - matVecMul (matSqrt S) G =
      matVecMul (matSqrt S) (F - G) := by
  funext i
  simp only [Pi.sub_apply, matVecMul, mul_sub, Finset.sum_sub_distrib]

/-- Inverse-square-root congruence carries the centered flux difference to
the normalized flux difference. -/
theorem matSqrt_inv_centered_flux_difference_eq {S A : Mat d}
    (hS : S.PosDef) (F G : Vec d) :
    matVecMul ((matSqrt S)⁻¹ * A * matTranspose (matSqrt S)⁻¹)
          (matVecMul (matSqrt S) F) - matVecMul (matSqrt S) G =
      matVecMul (matSqrt S)⁻¹
        (matVecMul A F - matVecMul S G) := by
  have hUnit : IsUnit (matSqrt S).det := isUnit_det_matSqrt hS
  have hSymm : matTranspose (matSqrt S)⁻¹ = (matSqrt S)⁻¹ := by
    rw [← matSqrt_inv hS]
    exact transpose_matSqrt_inv hS
  have hLeft :
      matVecMul ((matSqrt S)⁻¹ * A * matTranspose (matSqrt S)⁻¹)
          (matVecMul (matSqrt S) F) =
        matVecMul (matSqrt S)⁻¹ (matVecMul A F) := by
    rw [hSymm, matVecMul_mul, matVecMul_mul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hUnit, Matrix.mul_one]
  have hRight :
      matVecMul (matSqrt S) G =
        matVecMul (matSqrt S)⁻¹ (matVecMul S G) := by
    obtain ⟨_, hSq⟩ := matSqrt_spec hS.posSemidef
    have hMat : (matSqrt S)⁻¹ * S = matSqrt S := by
      calc
        (matSqrt S)⁻¹ * S =
            (matSqrt S)⁻¹ * (matSqrt S * matSqrt S) :=
          congrArg ((matSqrt S)⁻¹ * ·) hSq.symm
        _ = ((matSqrt S)⁻¹ * matSqrt S) * matSqrt S :=
          (Matrix.mul_assoc _ _ _).symm
        _ = matSqrt S := by
          rw [Matrix.nonsing_inv_mul _ hUnit, Matrix.one_mul]
    calc
      matVecMul (matSqrt S) G = matVecMul ((matSqrt S)⁻¹ * S) G := by rw [hMat]
      _ = matVecMul (matSqrt S)⁻¹ (matVecMul S G) :=
        (matVecMul_mul _ _ _).symm
  calc
    matVecMul ((matSqrt S)⁻¹ * A * matTranspose (matSqrt S)⁻¹)
          (matVecMul (matSqrt S) F) - matVecMul (matSqrt S) G =
        matVecMul (matSqrt S)⁻¹ (matVecMul A F) -
          matVecMul (matSqrt S) G := by rw [hLeft]
    _ = matVecMul (matSqrt S)⁻¹ (matVecMul A F) -
          matVecMul (matSqrt S)⁻¹ (matVecMul S G) := by rw [← hRight]
    _ = matVecMul (matSqrt S)⁻¹
          (matVecMul A F - matVecMul S G) := by
      funext i
      simp only [Pi.sub_apply, matVecMul, mul_sub, Finset.sum_sub_distrib]

/-- The preceding identity in the skew-centered convention of the
homogenization theorem. -/
theorem matSqrt_inv_skewCentered_flux_difference_eq {abar A : Mat d}
    (hS : (symmPart abar).PosDef) (F G : Vec d) :
    matVecMul
          ((matSqrt (symmPart abar))⁻¹ * (A - skewPart abar) *
            matTranspose (matSqrt (symmPart abar))⁻¹)
          (matVecMul (matSqrt (symmPart abar)) F) -
        matVecMul (matSqrt (symmPart abar)) G =
      matVecMul (matSqrt (symmPart abar))⁻¹
        (matVecMul (A - skewPart abar) F -
          matVecMul (symmPart abar) G) :=
  matSqrt_inv_centered_flux_difference_eq hS F G

end

end HighContrast
end HCPolySupport
