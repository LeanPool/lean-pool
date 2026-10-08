/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCutoffAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyEarlyAggregation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyInitialMeanAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Initial-chain-mean aggregation on convex domains

The initial ball mean is split at a common dyadic cutoff.  The boundary-side
part is supplied by the stopped chain, while the interior-side part is a
single comparison with the domain mean.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit coefficient for the initial-chain-mean comparison with the
domain mean. -/
@[expose]
def convexHardyInitialToDomainMeanAggregationFactor
    (d : ℕ) (rho Rad s beta : ℝ) (K : ℕ) (n : ℤ) : ℝ≥0∞ :=
  2 * (convexHardyPrefixGeometricFactor beta *
      convexHardyEarlyAggregationConstant d s beta rho Rad) +
    2 * convexHardyCutoffAggregationFactor d rho Rad s K n

end

end HighContrast
end HCPolySupport
