/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.EllipsoidGeometry
public import LeanPool.HighContrastHomogenization.Provider.Persistence.EuclideanTransfer
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormMaximum
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCellBounds
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.SharpBlockBounds.DiagonalSandwich

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.NormalizedBlockPositivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Positivity of constant comparison blocks

The full block matrix associated with a coefficient matrix is positive
definite as soon as the coefficient's symmetric part is positive definite.
The reflected block then gives the inverse action needed to calibrate the
primal and dual response loads.
-/

namespace HCPolySupport
namespace HighContrast

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The constant comparison block is positive definite whenever the symmetric
part of its coefficient matrix is positive definite. -/
theorem blockPosDef_constantBlockMatrix_of_posDef_symmPart
    {a0 : Mat d} (hS : (symmPart a0).PosDef) :
    BlockPosDef (Book.Ch02.constantBlockMatrix a0) := by
  rw [show Book.Ch02.constantBlockMatrix a0 = blockMatrixOfCoeff a0 by
    simp [Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff]]
  intro X hX
  rcases X with ⟨p, q⟩
  rw [blockMatrixOfCoeff_quadratic_eq]
  by_cases hp : p = 0
  · have hq : q ≠ 0 := by
      intro hq
      apply hX
      ext <;> simp [hp, hq]
    have hr : q - matVecMul (skewPart a0) p = q := by
      simp [hp, matVecMul_zero]
    have hfirst :
        0 ≤ vecDot p (matVecMul (symmPart a0) p) :=
      hS.posSemidef.dotProduct_mulVec_nonneg p
    have hsecond :
        0 < vecDot (q - matVecMul (skewPart a0) p)
          (matVecMul ((symmPart a0)⁻¹)
            (q - matVecMul (skewPart a0) p)) := by
      rw [hr]
      exact vecDot_matVecMul_pos_of_posDef hS.inv hq
    linarith only [hfirst, hsecond]
  · have hfirst :
        0 < vecDot p (matVecMul (symmPart a0) p) :=
      vecDot_matVecMul_pos_of_posDef hS hp
    have hsecond :
        0 ≤ vecDot (q - matVecMul (skewPart a0) p)
          (matVecMul ((symmPart a0)⁻¹)
            (q - matVecMul (skewPart a0) p)) :=
      hS.inv.posSemidef.dotProduct_mulVec_nonneg _
    linarith only [hfirst, hsecond]

private theorem blockMatMul_blockReflect_blockMatrixOfCoeff_eq_id_of_posDef_symmPart
    {a0 : Mat d} (hS : (symmPart a0).PosDef) :
    blockMatMul (blockMatrixOfCoeff a0) (blockReflect (blockMatrixOfCoeff a0)) =
      blockIdentity d := by
  have hsdet : IsUnit (symmPart a0).det := isUnit_det_of_posDef hS
  have hss : symmPart a0 * (symmPart a0)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hsdet
  have hss' : (symmPart a0)⁻¹ * symmPart a0 = 1 :=
    Matrix.nonsing_inv_mul _ hsdet
  have hkt : matTranspose (skewPart a0) = -(skewPart a0) :=
    matTranspose_skewPart a0
  refine blockMat_ext ?_ ?_ ?_ ?_
  · simp only [blockMatMul, blockReflect_upperLeft, blockReflect_lowerLeft,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]
    have h :
        (symmPart a0 + -skewPart a0 * (symmPart a0)⁻¹ * skewPart a0) *
              (symmPart a0)⁻¹ +
            -(-skewPart a0 * (symmPart a0)⁻¹) *
              -(-skewPart a0 * (symmPart a0)⁻¹) =
          symmPart a0 * (symmPart a0)⁻¹ := by
      noncomm_ring
    rw [h, hss]
  · simp only [blockMatMul, blockReflect_upperRight, blockReflect_lowerRight,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]
    have h :
        (symmPart a0 + -skewPart a0 * (symmPart a0)⁻¹ * skewPart a0) *
              -((symmPart a0)⁻¹ * skewPart a0) +
            -(-skewPart a0 * (symmPart a0)⁻¹) *
              (symmPart a0 + -skewPart a0 * (symmPart a0)⁻¹ * skewPart a0) =
          -(symmPart a0 * (symmPart a0)⁻¹ * skewPart a0) +
            skewPart a0 * ((symmPart a0)⁻¹ * symmPart a0) := by
      noncomm_ring
    rw [h, hss, hss']
    simp
  · simp only [blockMatMul, blockReflect_upperLeft, blockReflect_lowerLeft,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]
    noncomm_ring
  · simp only [blockMatMul, blockReflect_upperRight, blockReflect_lowerRight,
      blockMatrixOfCoeff, blockIdentity, blockDiag]
    rw [hkt]
    have h :
        -((symmPart a0)⁻¹ * skewPart a0) *
              -((symmPart a0)⁻¹ * skewPart a0) +
            (symmPart a0)⁻¹ *
              (symmPart a0 + -skewPart a0 * (symmPart a0)⁻¹ * skewPart a0) =
          (symmPart a0)⁻¹ * symmPart a0 := by
      noncomm_ring
    rw [h, hss']

/-- Applying a constant block after its reflected block recovers the input. -/
theorem blockMatVecMul_constantBlockMatrix_blockReflect_inv_of_posDef_symmPart
    {a0 : Mat d} (hS : (symmPart a0).PosDef) (Y : BlockVec d) :
    blockMatVecMul (Book.Ch02.constantBlockMatrix a0)
        (blockMatVecMul (blockReflect (Book.Ch02.constantBlockMatrix a0)) Y) = Y := by
  rw [← blockMatVecMul_blockMatMul]
  simpa [Book.Ch02.constantBlockMatrix, blockMatrixOfCoeff,
    blockMatVecMul_blockIdentity] using congrArg
    (fun A : BlockMat d => blockMatVecMul A Y)
    (blockMatMul_blockReflect_blockMatrixOfCoeff_eq_id_of_posDef_symmPart hS)

end

end HighContrast
end HCPolySupport
