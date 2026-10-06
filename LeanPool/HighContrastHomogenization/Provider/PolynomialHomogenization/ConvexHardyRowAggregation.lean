/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCellInitialAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyInitialMeanAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyRowAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fractional Hardy aggregation on convex domains

The initial Whitney-cell comparison and a stopped convex ball chain control
the centered inverse-scale weighted squared-deviation term in the positive
fractional row norm.  The existential form chooses all auxiliary geometric
parameters before the function being estimated.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit coefficient for the centered positive Whitney-row energy. -/
@[expose]
def convexHardyWhitneyRowAggregationFactor
    (d : ℕ) (rho Rad s beta : ℝ) (K : ℕ) (n : ℤ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal ((Real.sqrt d) ^ ((d : ℝ) + 2 * s)) +
    4 * convexHardyCellInitialAggregationConstant d s rho Rad +
    4 * convexHardyInitialToDomainMeanAggregationFactor
      d rho Rad s beta K n

end

end HighContrast
end HCPolySupport
