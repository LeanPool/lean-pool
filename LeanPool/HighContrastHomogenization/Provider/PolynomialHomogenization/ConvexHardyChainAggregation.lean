/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyChainMean
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyShadow
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyBallChain
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyRowFluctuation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyScaleSummation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyChainAggregation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Aggregation of the small-radius part of convex Hardy chains

Successive chain links are aggregated only while their straight-chain shadows
fit inside the outer sandwich ball.  The complementary links are retained as
an explicit late-link term.  Thus the homogeneous shadow estimate is never
used beyond its geometric range.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal Matrix

attribute [local instance] Classical.propDecidable

noncomputable section

variable {d : ℕ}

/-- The Euclidean cross-diameter multiplier for two successive chain balls. -/
@[expose]
def convexHardyChainAggregationDistanceFactor
    (d : ℕ) (rho Rad : ℝ) : ℝ :=
  3 + Real.sqrt d * (Rad / rho)

end

end HighContrast
end HCPolySupport
