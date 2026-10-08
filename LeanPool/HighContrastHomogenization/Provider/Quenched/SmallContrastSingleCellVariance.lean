/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSourceMoment
public import LeanPool.HighContrastHomogenization.Provider.Transport.WindowCenteredBound

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSingleCellVariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The single-cell reference variance at arbitrary enclosed scales

The per-scale fluctuation carrier of the weak cap is bounded by an explicit
constant at every enclosed scale: the coarse block and the adapted mean are
both dominated by the scaled reference with the normalized-source-scale
factor, the Loewner sandwich bounds the normalized Schatten size pointwise,
and the crude second moment of the normalized source scale integrates the
bound.  This is the printed crude-moment display for the single-cell
variance, window-free.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder ENNReal

noncomputable section

variable {d : ℕ}

/-- The second crude moment constant of the normalized source scale. -/
@[expose]
def sourceMomentTwo (K : ℝ) : ℝ :=
  1 + 2 * ((2 : ℕ) : ℝ) * (1 + Real.log (growthBar K)) *
    growthBar K ^ IndependentSums.natTriangular 2

end

end HCPolySupport.HighContrast.Quenched
