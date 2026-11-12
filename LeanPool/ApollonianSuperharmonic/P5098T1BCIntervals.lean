/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P5098T1PeriodWindow
public import Mathlib.Tactic.IntervalCases

-- [TABLET NODE: P5098T1BCIntervals]

/-!
# P5098T1BCIntervals

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5098T1BCIntervals (r s m k : Int) (hs : 2 ≤ s) (hrs : s < r)
    (h : ((-s < r - s - m * (r + s) + k * s ∧ r - s - m * (r + s) + k * s < r) ∧
        (-s ≤ -s + (r + s) * k ∧ -s + (r + s) * k ≤ r)) ∨
      ((-s ≤ r - s - m * (r + s) + k * s ∧ r - s - m * (r + s) + k * s ≤ r) ∧
        (-s < -s + (r + s) * k ∧ -s + (r + s) * k < r))) :
    m = 0 ∧ k = 0 := by
-- BODY
  have hw := P5098T1PeriodWindow (r + s) s m k (by omega) (by omega)
    (by omega) (by omega)
  obtain ⟨⟨hk0, hk1⟩, hm0, hm1⟩ := hw
  interval_cases k <;> interval_cases m <;> norm_num at h <;> omega

end ApollonianSuperharmonic

end
