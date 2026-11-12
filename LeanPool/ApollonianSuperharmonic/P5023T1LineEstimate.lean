/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P5023T1LineEstimate]

/-!
# P5023T1LineEstimate

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5023T1LineEstimate (R a b t u v : ℝ)
    (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha1 : a ≤ 1) (hb1 : b ≤ 1)
    (ht : min u v < t ∧ t < max u v)
    (hu : (t - u) ^ 2 = 4 * R * a) (hv : (t - v) ^ 2 = 4 * R * b) :
    |u - v| = 2 * Real.sqrt (R * a) + 2 * Real.sqrt (R * b) ∧
      |u - v| ≤ 4 * Real.sqrt R := by
-- BODY
  have hsu : |t - u| = 2 * Real.sqrt (R * a) := by
    have hs := Real.sq_sqrt (mul_nonneg hR ha)
    have habs := sq_abs (t - u)
    have hn := abs_nonneg (t - u)
    have hp := Real.sqrt_nonneg (R * a)
    nlinarith
  have hsv : |t - v| = 2 * Real.sqrt (R * b) := by
    have hs := Real.sq_sqrt (mul_nonneg hR hb)
    have habs := sq_abs (t - v)
    have hn := abs_nonneg (t - v)
    have hp := Real.sqrt_nonneg (R * b)
    nlinarith
  have hsum : |u - v| = |t - u| + |t - v| := by
    rcases le_total u v with huv | hvu
    · rw [min_eq_left huv, max_eq_right huv] at ht
      rw [abs_of_nonpos (sub_nonpos.mpr huv),
        abs_of_pos (sub_pos.mpr ht.1), abs_of_neg (sub_neg.mpr ht.2)]
      ring
    · rw [min_eq_right hvu, max_eq_left hvu] at ht
      rw [abs_of_nonneg (sub_nonneg.mpr hvu),
        abs_of_neg (sub_neg.mpr ht.2), abs_of_pos (sub_pos.mpr ht.1)]
      ring
  have hsa : Real.sqrt (R * a) ≤ Real.sqrt R :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left ha1 hR])
  have hsb : Real.sqrt (R * b) ≤ Real.sqrt R :=
    Real.sqrt_le_sqrt (by nlinarith [mul_le_mul_of_nonneg_left hb1 hR])
  rw [hsu, hsv] at hsum
  exact ⟨hsum, by linarith⟩

end ApollonianSuperharmonic

end
