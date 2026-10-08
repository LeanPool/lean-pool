/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyChainMean
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexHardyRowFluctuation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexHardyCellRawMean

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Raw comparison of a Whitney-cell mean with its initial chain ball

The first step of a convex Hardy chain compares the mean on a Whitney cell
with the mean on its initial interior ball.  The estimate retains the raw
cross difference, as do the later links of the chain.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit lower ball volume is bounded by the volume of every
Euclidean ball of the corresponding radius. -/
theorem convexHardyBallVolumeLower_le_volume_euclideanBallAt
    (hd : 1 ≤ d) (c : Vec d) {r : ℝ} (hr : 0 < r) :
    convexHardyBallVolumeLower d r ≤ volume (euclideanBallAt c r) := by
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hdreal : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hsqrtd : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hquot : 0 < r / Real.sqrt d := div_pos hr hsqrtd
  rw [convexHardyBallVolumeLower, ← volume_ball_eq c hquot]
  exact measure_mono (metricBall_subset_euclideanBallAt hdpos c hr)

end

end HighContrast
end HCPolySupport
