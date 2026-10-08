/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.Geometry

/-!
# High-contrast homogenization: Provider.Quenched.ThresholdCalibration

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Threshold calibration for the quenched endgame

This is the numerical choice behind the small-contrast threshold of
`ss.algebraic.convergence`.  Once a
positive small-contrast threshold has been fixed, the two remaining
thresholds can be chosen before any exponent or probability law.
-/

namespace HCPolySupport.HighContrast.Quenched

/-- Given a positive small-contrast threshold, there are positive rebasing and
entry thresholds satisfying the endgame calibration. -/
theorem exists_threshold_calibration_below (cSc : ℝ) (hcSc : 0 < cSc) :
    ∃ delta₀ cEnd : ℝ,
      delta₀ ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < cEnd ∧
        (1 + delta₀) ^ 2 * (1 + cEnd) ≤ 1 + cSc := by
  let e : ℝ := min (1 / 2) (cSc / 8)
  have he0 : 0 < e := by
    dsimp [e]
    exact lt_min (by norm_num) (by linarith only [hcSc])
  have he2 : e ≤ 1 / 2 := by
    exact min_le_left _ _
  have heSc : e ≤ cSc / 8 := by
    exact min_le_right _ _
  have he1 : e ≤ 1 := by
    linarith only [he2]
  have heSq : e ^ 2 ≤ e := by
    nlinarith only [he0, he1]
  have heCube : e ^ 3 ≤ e := by
    calc
      e ^ 3 = e * e ^ 2 := by ring
      _ ≤ e * e := mul_le_mul_of_nonneg_left heSq he0.le
      _ = e ^ 2 := by ring
      _ ≤ e := heSq
  refine ⟨e, e, ⟨he0, ?_⟩, he0, ?_⟩
  · linarith only [he2]
  calc
    (1 + e) ^ 2 * (1 + e) = 1 + 3 * e + 3 * e ^ 2 + e ^ 3 := by ring
    _ ≤ 1 + 7 * e := by linarith only [heSq, heCube]
    _ ≤ 1 + 7 * (cSc / 8) := by linarith only [heSc]
    _ ≤ 1 + cSc := by linarith only [hcSc]

end HCPolySupport.HighContrast.Quenched
