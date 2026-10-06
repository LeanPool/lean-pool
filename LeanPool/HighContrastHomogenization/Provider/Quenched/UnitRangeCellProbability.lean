/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeBlockReassembly
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCellRenormalization
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeInnerCells
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeNormalizedCutoff

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeCellProbability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The probabilistic normalized cell estimate

The unit-range concentration bound is applied at a shifted parameter so that
the finite block-entry union bound is absorbed into the Gaussian gauge.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The dimensional parameter shift absorbing whole-block reassembly. -/
@[expose]
def unitRangeRenormShift (d : ℕ) : ℝ :=
  Real.log (4 * (d : ℝ) ^ 2 + 1) / (2 * frGaugeConst d)

theorem unitRangeRenormShift_nonneg (d : ℕ) : 0 ≤ unitRangeRenormShift d := by
  refine div_nonneg (Real.log_nonneg ?_) ?_
  · nlinarith only [sq_nonneg ((d : ℝ))]
  · exact (mul_nonneg (by norm_num) (frGaugeConst_pos d).le)

end

end Quenched
end HighContrast
end HCPolySupport
