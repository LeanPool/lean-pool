/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCellRawMean
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyRowFluctuation
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyCellInitialAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Aggregating the initial cell-to-ball comparisons

The first link from a Whitney cell to its ball chain is charged through the
cell coordinate of a disjoint family of product rectangles.  Its scale
weight cancels the inverse cell and ball volumes without any summation loss.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal
open scoped Function

noncomputable section

variable {d : ℕ}

/-- The scale-free coefficient for all initial cell-to-ball comparisons. -/
@[expose]
def convexHardyCellInitialAggregationConstant
    (d : ℕ) (s rho Rad : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((Real.sqrt d) ^ d *
      Real.rpow
        (2 * (1 + Real.sqrt d * (1 + Rad / rho)))
        ((d : ℝ) + 2 * s))

end

end HighContrast
end HCPolySupport
