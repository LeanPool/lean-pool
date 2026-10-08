/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyChainAggregation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyEarlyAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section
/-!
# Fractional aggregation of the small-radius Hardy-chain links

The homogeneous part of the coherent ball chains is summed through a
pointwise shadow estimate.  The physical pair distance is retained until the
dyadic scale sum, avoiding a logarithmic loss over the remaining chain depth.
-/

namespace HCPolySupport
namespace HighContrast
open MeasureTheory
open scoped ENNReal Matrix
attribute [local instance] Classical.propDecidable

noncomputable section
variable {d : ℕ}

/-- The explicit coefficient for aggregating all small-radius chain links. -/
@[expose]
def convexHardyEarlyAggregationConstant
    (d : ℕ) (s beta rho Rad : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (convexHardyShadowRowConstant d rho Rad
          (convexHardyChainAggregationDistanceFactor d rho Rad) *
        ((d : ℝ) / 8) ^ d) *
    convexHardyScaleSummationConstant d s beta
      (convexHardyChainAggregationDistanceFactor d rho Rad)

end
end HighContrast
end HCPolySupport
