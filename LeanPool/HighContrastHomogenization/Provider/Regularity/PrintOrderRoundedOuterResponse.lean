/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineMap
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedOuterScaleFubini
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedNormalizedRootCellResponseMax
public import LeanPool.HighContrastHomogenization.Provider.Response.AdaptedLinearOscillation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.PrintOrderCertificateInhabitation

/-!
# High-contrast homogenization: Provider.Regularity.PrintOrderRoundedOuterResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded outer response at the printed order

The order-generic response maximum theorem applies directly at
`(1 + g) / 4`.  This interface keeps the resulting `g`-dependent geometric
discount instead of replacing it by the small-order constant six.
-/

namespace HCPolySupport
namespace HighContrast

open scoped BigOperators Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The inverse boundary-layer discount at the printed order is finite for
every `g ∈ [0,1)`. -/
theorem printOrder_outerGeometricDiscount_inv_nonneg
    {g : ℝ} (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    0 ≤ (Book.Ch02.geometricDiscount
      (1 - 2 * printCertificateOrder g) 1)⁻¹ := by
  have hgapPos : 0 < 1 - 2 * printCertificateOrder g := by
    dsimp only [printCertificateOrder]
    linarith only [hg.2]
  have hdiscPos :
      0 < Book.Ch02.geometricDiscount
        (1 - 2 * printCertificateOrder g) 1 := by
    simpa only [Book.Ch02.geometricDiscount_eq_old] using
      (HCPolySupport.geometricDiscount_pos (by
        simpa only [mul_one] using hgapPos))
  exact inv_nonneg.mpr hdiscPos.le

end

end HighContrast
end HCPolySupport
