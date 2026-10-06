/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Initialization.Boundary
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CommonQuantitativeAffineScale
public import LeanPool.HighContrastHomogenization.Provider.Regularity.PrintOrderRoundedOuterResponse

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedResponseScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded response scale at the printed fractional order

The boundary-layer discount is retained as a function of the exponent chosen
after `g`.  Enlarging by the corresponding affine multiplier absorbs the
complete rounded-cell response loss without imposing a small-order bound.
-/

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The squared rounded-response loss at the printed order. -/
@[expose]
noncomputable def printOrderRoundedResponseAffineConstantSq
    (d : ℕ) (g : ℝ) : ℝ :=
  max 1 (6 * (d : ℝ) * Real.sqrt d * (101 / 100 : ℝ)) *
    (Book.Ch02.geometricDiscount
      (1 - 2 * printCertificateOrder g) 1)⁻¹ *
    (1 + 3 * ((100 / 99 : ℝ) * Real.sqrt d))

/-- The rounded-response affine loss at the printed order. -/
@[expose]
noncomputable def printOrderRoundedResponseAffineConstant
    (d : ℕ) (g : ℝ) : ℝ :=
  Real.sqrt (printOrderRoundedResponseAffineConstantSq d g)

/-- The printed-order rounded-response affine loss is positive. -/
theorem printOrderRoundedResponseAffineConstant_pos
    (d : ℕ) {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 < printOrderRoundedResponseAffineConstant d g := by
  unfold printOrderRoundedResponseAffineConstant
    printOrderRoundedResponseAffineConstantSq
  apply Real.sqrt_pos.2
  have hfirst : 0 < max 1
      (6 * (d : ℝ) * Real.sqrt d * (101 / 100 : ℝ)) :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hgap : 0 < 1 - 2 * printCertificateOrder g :=
    (printOrder_margins hg).2.2.2.2.2.2.2.2
  have hdiscount : 0 <
      (Book.Ch02.geometricDiscount
        (1 - 2 * printCertificateOrder g) 1)⁻¹ := by
    apply inv_pos.mpr
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      (HCPolySupport.geometricDiscount_pos (by
        simpa only [mul_one] using hgap))
  have hlast : 0 < 1 + 3 * ((100 / 99 : ℝ) * Real.sqrt d) := by
    positivity
  exact mul_pos (mul_pos hfirst hdiscount) hlast

private theorem multiplier_rpow_mul_ratio_eq_rpow_mul_scale
    {mult kappa x r : ℝ} (hmult : 0 < mult)
    (hx : 0 < x) (hr : 0 < r) :
    mult ^ kappa * (r / x) ^ (-kappa) =
      (r / (mult * x)) ^ (-kappa) := by
  have hratio : r / (mult * x) = (r / x) / mult := by
    field_simp [hmult.ne', hx.ne']
  rw [hratio, Real.div_rpow (div_nonneg hr.le hx.le) hmult.le,
    Real.rpow_neg hmult.le, div_inv_eq_mul, mul_comm]

end

end HighContrast
end HCPolySupport
