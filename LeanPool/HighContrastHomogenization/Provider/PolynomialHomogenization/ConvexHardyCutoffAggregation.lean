/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCellRawMean
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyChainAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyCoreMean

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyCutoffAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fixed-cutoff aggregation for convex Hardy chains

A common dyadic cutoff replaces the uniformly interior tail of every ball
chain by one comparison with the domain mean.  Short chains use their initial
ball, so the construction has no exceptional row.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

namespace ConvexHardyBallChain

end ConvexHardyBallChain

/-- The explicit normalized cutoff-mean aggregation factor. -/
@[expose]
def convexHardyCutoffAggregationFactor
    (d : ℕ) (rho Rad s : ℝ) (K : ℕ) (n : ℤ) : ℝ≥0∞ :=
  convexHardyCoreRowMassFactor d rho s n *
    convexHardyCoreMeanFactor d (convexHardyDyadicRadius rho K) Rad s

/-- The infinite geometric-head factor used for the boundary-scale chain
prefix. -/
@[expose]
def convexHardyPrefixGeometricFactor (beta : ℝ) : ℝ≥0∞ :=
  (1 - ENNReal.ofReal (Real.rpow 2 (-beta)))⁻¹

end

end HighContrast
end HCPolySupport
