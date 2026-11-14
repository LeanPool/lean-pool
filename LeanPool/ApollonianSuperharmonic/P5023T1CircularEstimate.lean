/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Tactic.Positivity

public import Mathlib.Analysis.Real.Sqrt

-- [TABLET NODE: P5023T1CircularEstimate]

/-!
# P5023T1CircularEstimate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5023T1CircularEstimate (r R : ℝ) (hR : 0 < R)
    (hRr : R < r) (hr1 : r ≤ 1) :
    2 * r * Real.sqrt (1 - ((r - R) / (r + R)) ^ 2) ≤ 4 * Real.sqrt R := by
-- BODY
  have hden : 0 < r + R := by linarith
  have hquot : |(r - R) / (r + R)| ≤ 1 := by
    rw [abs_div, abs_of_pos hden]
    apply (div_le_iff₀ hden).2
    rw [abs_le]
    constructor <;> linarith
  have hrad : 0 ≤ 1 - ((r - R) / (r + R)) ^ 2 := by
    have hprod : 0 ≤
        (1 - |(r - R) / (r + R)|) * (1 + |(r - R) / (r + R)|) :=
      mul_nonneg (sub_nonneg.mpr hquot) (by positivity)
    rw [← sq_abs]
    nlinarith
  have hidentity :
      1 - ((r - R) / (r + R)) ^ 2 = 4 * r * R / (r + R) ^ 2 := by
    field_simp
    ring
  have hrSq : r ^ 2 ≤ (r + R) ^ 2 := by nlinarith [sq_nonneg R]
  have hrCube : r ^ 3 ≤ (r + R) ^ 2 := by
    calc
      r ^ 3 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
      _ ≤ (r + R) ^ 2 := hrSq
  have hmain :
      (2 * r * Real.sqrt (1 - ((r - R) / (r + R)) ^ 2)) ^ 2 ≤
        (4 * Real.sqrt R) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt hrad, Real.sq_sqrt hR.le]
    rw [hidentity]
    have hdenSq : 0 < (r + R) ^ 2 := sq_pos_of_pos hden
    field_simp [ne_of_gt hdenSq]
    nlinarith [mul_le_mul_of_nonneg_right hrCube hR.le]
  have hright : 0 ≤ 4 * Real.sqrt R := by positivity
  nlinarith

end ApollonianSuperharmonic

end
