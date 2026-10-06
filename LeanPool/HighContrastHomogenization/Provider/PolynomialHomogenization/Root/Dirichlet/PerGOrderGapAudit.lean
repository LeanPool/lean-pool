/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Certificate.PrintOrderCertificate
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupplyAssembly.PrintDirectResponseWindowComposition

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.Root.Dirichlet.PerGOrderGapAudit

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The gap between the row order and twice the response order

The row order and the response order of the printed route are distinct affine
functions of the exponent, and the geometric factor that closes every
descendant sum in the certificate chain is read at their difference.  The
difference is strictly positive on the whole admissible window and degenerates
only at its excluded right endpoint, where the geometric factor has no value.

The estimate below fixes that: the row order is strictly below twice the
certificate order and strictly below twice the response-window order, at every
admissible exponent, with the gaps computed exactly; and the geometric factor
of the absorption prefactor is therefore positive.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

noncomputable section

/-! ## The exact gaps -/

/-- The gap between twice the response-window order and the row order is
`(1 - g) / 8`. -/
theorem two_mul_responseWindowOrder_sub_printRowOrder (g : ℝ) :
    2 * responseWindowOrder g - Certificate.printRowOrder g = (1 - g) / 8 := by
  rw [responseWindowOrder, Certificate.printRowOrder]
  ring

/-! ## The geometric factor of the absorption prefactor -/

/-- The geometric factor that closes the descendant sums is positive exactly
because the gap above is positive.  This discharges the hypothesis of the
prefactor estimate at the printed orders. -/
theorem one_sub_rpow_neg_gap_pos_responseWindow {g : ℝ} (hg : g < 1) :
    0 < 1 - (3 : ℝ) ^
      (-(2 * responseWindowOrder g - Certificate.printRowOrder g)) := by
  have hgap : 2 * responseWindowOrder g - Certificate.printRowOrder g =
      (1 - g) / 8 := two_mul_responseWindowOrder_sub_printRowOrder g
  have hpos : (0 : ℝ) < (1 - g) / 8 := by linarith only [hg]
  have hlt : (3 : ℝ) ^ (-((1 - g) / 8)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hpos])
  rw [hgap]
  linarith only [hlt]

end

end RowSupply
end HighContrast
end HCPolySupport
