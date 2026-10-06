/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyChainMean
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyWhitneySystem
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyCoreMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Inverse-scale row mass in a convex Whitney system

The Whitney row-volume estimate and a geometric series control the total
normalized inverse-scale mass of the cells. The retained factors support
the fixed-cutoff aggregation of boundary and top rows.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The loss in comparing the mean on the common interior ball with the
domain mean. -/
@[expose]
def convexHardyCoreMeanFactor (d : ℕ) (rho Rad s : ℝ) : ℝ≥0∞ :=
  2 * (convexHardyBallVolumeLower d rho)⁻¹ *
    ENNReal.ofReal ((2 * Rad) ^ ((d : ℝ) + 2 * s))

/-- The ratio of the inverse-scale Whitney row series. -/
@[expose]
def convexHardyCoreRowRatio (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / 3 : ℝ) ^ (-2 * s)) * ENNReal.ofReal (1 / 3 : ℝ)

/-- The normalized total inverse-scale volume bound for all Whitney rows up
to the top scale `n`. -/
@[expose]
def convexHardyCoreRowMassFactor (d : ℕ) (rho s : ℝ) (n : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (((3 : ℝ) ^ n) ^ (-2 * s)) +
    ENNReal.ofReal (((3 : ℝ) ^ (n - 1)) ^ (-2 * s)) *
      ENNReal.ofReal
        (6 * (d : ℝ) * Real.sqrt d * (3 : ℝ) ^ (n - 1) / rho) *
        (1 - convexHardyCoreRowRatio s)⁻¹

end

end HighContrast
end HCPolySupport
