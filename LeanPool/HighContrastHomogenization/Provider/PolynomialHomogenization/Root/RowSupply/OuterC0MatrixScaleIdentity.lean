/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.FormulaicAnchoredResidualFrameRate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.OuterC0MatrixScaleIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The matrix scale of the outer Dirichlet constant

The residual affine filling coefficient contains the absolute scalar scale of
the symmetric reference matrix.  This file makes that dependence explicit.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The cross-grid matrix in the observation filling is a scalar multiple of
the identity.  Its scalar is the residual dilation times the absolute
normalization scale of the symmetric reference matrix. -/
theorem epsilonAffineGrid_inv_mul_normalizedRoot_eq
    [NeZero d] {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {abar : Mat d} (hS : (symmPart abar).PosDef) :
    (epsilonAffineGrid epsilon abar)⁻¹ *
        Selection.normalizedRoot (symmPart abar) =
      (epsilon * Real.sqrt (specBound (symmPart abar)⁻¹)) • (1 : Mat d) := by
  have hM : (matSqrt (symmPart abar)).PosDef := posDef_matSqrt hS
  rw [epsilonAffineGrid, Selection.normalizedRoot_eq,
    Response.inv_smul_posDef hM (inv_pos.mpr hepsilon), inv_inv,
    Matrix.smul_mul, Matrix.mul_smul, ← matSqrt_inv hS,
    matSqrt_inv_mul_matSqrt hS, smul_smul]

/-- Consequently, the norm entering the filling coefficient retains the same
absolute normalization scale. -/
theorem norm_epsilonAffineGrid_inv_mul_normalizedRoot
    [NeZero d] {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {abar : Mat d} (hS : (symmPart abar).PosDef) :
    ‖(epsilonAffineGrid epsilon abar)⁻¹ *
        Selection.normalizedRoot (symmPart abar)‖ =
      epsilon * Real.sqrt (specBound (symmPart abar)⁻¹) := by
  rw [epsilonAffineGrid_inv_mul_normalizedRoot_eq hepsilon hS, norm_smul,
    Real.norm_eq_abs, abs_of_pos
      (mul_pos hepsilon (Real.sqrt_pos.mpr (normalizedRootScale_pos hS))),
    norm_one, mul_one]

/-- Exact expansion of the matrix-dependent observation coefficient. -/
theorem observationFillingCoefficient_eq_absoluteScale
    [NeZero d] {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {abar : Mat d} (hS : (symmPart abar).PosDef) :
    observationFillingCoefficient d epsilon abar =
      max 1 (6 * (d : ℝ) * Real.sqrt d *
        (epsilon * Real.sqrt (specBound (symmPart abar)⁻¹))) := by
  unfold observationFillingCoefficient
  rw [norm_epsilonAffineGrid_inv_mul_normalizedRoot hepsilon hS]

end

end RowSupply
end HighContrast
end HCPolySupport
