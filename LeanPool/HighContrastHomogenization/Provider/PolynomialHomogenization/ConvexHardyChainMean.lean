/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyBallChain
public import LeanPool.HighContrastHomogenization.Analytic.EuclideanAmbient
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalMeanJump
public import LeanPool.HighContrastHomogenization.Analytic.AntiVacuityInstances

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyChainMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Fractional control of means along convex ball chains

Successive balls in a convex Hardy chain have doubling radii and quantitatively
nearby centers.  The fractional mean-jump estimate therefore controls each
successive change of mean by the Gagliardo energy on the union of the two
balls.  Finite vector telescoping then compares the initial mean with the mean
on the fixed core ball.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit lower bound for the volume of a Euclidean ball of radius
`r`, obtained from the concentric ambient sup-norm ball. -/
@[expose]
def convexHardyBallVolumeLower (d : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * (r / Real.sqrt d)) ^ d)

end

end HighContrast
end HCPolySupport
