/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.L2RowAlgebra
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledObservationComparisonPricing
public import LeanPool.HighContrastHomogenization.Provider.Regularity.ResponseExponentGap

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.ResponseAttainabilityPricing

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Response times attainability pricing on ruled observation cubes

The Dirichlet flux right-hand side contains the outer-exponent-one response
at the regularity order.  A strict exponent gap converts it to the
outer-exponent-two response at a lower order.  The result is a product of that
response and the Dirichlet energy price, exactly matching the two factors in
the deterministic homogenization estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The geometric-series loss in the conversion from an
outer-exponent-two response at order `b` to an outer-exponent-one response at
the strictly larger order `r`. -/
@[expose]
noncomputable def responseOneFromTwoGapFactor (b r : ℝ) : ℝ :=
  Book.Ch02.geometricDiscount r 1 *
    (Real.sqrt (Book.Ch02.geometricDiscount (r - b) 2))⁻¹ *
    (Real.sqrt (Book.Ch02.geometricDiscount b 2))⁻¹

theorem responseOneFromTwoGapFactor_nonneg
    {b r : ℝ} (hb : 0 < b) (hbr : b < r) :
    0 ≤ responseOneFromTwoGapFactor b r := by
  have hr : 0 < r := hb.trans hbr
  have hgap : 0 < r - b := sub_pos.mpr hbr
  have hrDiscount : 0 ≤ Book.Ch02.geometricDiscount r 1 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      (geometricDiscount_pos (by simpa only [mul_one] using hr)).le
  have hgapDiscount :
      0 ≤ Book.Ch02.geometricDiscount (r - b) 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      (geometricDiscount_pos
        (mul_pos hgap (by norm_num : (0 : ℝ) < 2))).le
  have hbDiscount : 0 ≤ Book.Ch02.geometricDiscount b 2 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      (geometricDiscount_pos
        (mul_pos hb (by norm_num : (0 : ℝ) < 2))).le
  unfold responseOneFromTwoGapFactor
  exact mul_nonneg
    (mul_nonneg hrDiscount (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

end

end RowSupply
end HighContrast
end HCPolySupport
