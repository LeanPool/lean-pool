/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Entry.EuclideanAdapter
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineMap
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedOuterScaleFubini
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Entry.AdapterQuadratic
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootCellResponseMax
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedLinearOscillation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.EllipticityControl
public import LeanPool.HighContrastHomogenization.Provider.Regularity.QuantitativeGoodTail
public import LeanPool.HighContrastHomogenization.Provider.Initialization.Boundary

/-!
# High-contrast homogenization: Provider.Regularity.RoundedOuterSpatialResponsePowerTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quantitative power tails for rounded outer response maxima

The retained scalar identity power tail is applied at the enclosing
normalized-root parent.  The parent shift and rounded boundary losses are
then bounded by one dimension-only affine constant times the witness
eccentricity.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open scoped BigOperators Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Squared dimension-only constant for the rounded outer-response affine estimates. -/
@[expose]
public noncomputable def roundedOuterResponseAffineConstantSq (d : ℕ) : ℝ :=
  max 1
      (6 * (d : ℝ) * Real.sqrt d * (101 / 100 : ℝ)) *
    10 *
      (1 + 3 * ((100 / 99 : ℝ) * Real.sqrt d))

/-- A dimension-only constant absorbing the rounded boundary row and the
normalized-root parent shift on the weak-error scale. -/
@[expose]
noncomputable def roundedOuterResponseAffineConstant (d : ℕ) : ℝ :=
  Real.sqrt (roundedOuterResponseAffineConstantSq d)

theorem roundedOuterResponseAffineConstant_pos (d : ℕ) :
    0 < roundedOuterResponseAffineConstant d := by
  unfold roundedOuterResponseAffineConstant roundedOuterResponseAffineConstantSq
  apply Real.sqrt_pos.2
  have hfirst : 0 < max 1
      (6 * (d : ℝ) * Real.sqrt d * (101 / 100 : ℝ)) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hlast : 0 < 1 + 3 * ((100 / 99 : ℝ) * Real.sqrt d) := by
    positivity
  exact mul_pos (mul_pos hfirst (by norm_num)) hlast

end

end Transport
end HighContrast
end HCPolySupport
