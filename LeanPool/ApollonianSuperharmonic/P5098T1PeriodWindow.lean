/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P5098T1PeriodWindow]

/-!
# P5098T1PeriodWindow

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5098T1PeriodWindow (q s m k : Int) (hs : 0 < s) (hsq : s < q)
    (hy : -q ≤ q * k ∧ q * k ≤ q)
    (hx : -q ≤ -(m * q) + k * s ∧ -(m * q) + k * s ≤ q) :
    (-1 ≤ k ∧ k ≤ 1) ∧ (-1 ≤ m ∧ m ≤ 1) := by
-- BODY
  have hq : 0 < q := by omega
  have hk : -1 ≤ k ∧ k ≤ 1 := by
    constructor
    · by_contra h
      have hh : k ≤ -2 := by omega
      have := mul_le_mul_of_nonneg_left hh hq.le
      nlinarith [hy.1]
    · by_contra h
      have hh : 2 ≤ k := by omega
      have := mul_le_mul_of_nonneg_left hh hq.le
      nlinarith [hy.2]
  have hks : -s ≤ k * s ∧ k * s ≤ s := by
    constructor
    · have := mul_le_mul_of_nonneg_right hk.1 hs.le
      linarith
    · have := mul_le_mul_of_nonneg_right hk.2 hs.le
      linarith
  refine ⟨hk, ?_, ?_⟩
  · by_contra h
    have hh : m ≤ -2 := by omega
    have := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith [hx.2, hks.1]
  · by_contra h
    have hh : 2 ≤ m := by omega
    have := mul_le_mul_of_nonneg_right hh hq.le
    nlinarith [hx.1, hks.2]

end ApollonianSuperharmonic

end
