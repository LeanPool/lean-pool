/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.P3019T1ChamberStripGeometry
public import Mathlib.Tactic.LinearCombination

-- [TABLET NODE: P3019T1UnimodularStripWindow]

/-!
# P3019T1UnimodularStripWindow

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3019T1UnimodularStripWindow
    (x : Int × Int) (a b c d : Int)
    (hab : 0 ≤ b ∧ b ≤ a) (hcd : 0 ≤ d ∧ d ≤ c)
    (horient : a * d - b * c = -1) :
    0 < a ∧ 0 < c ∧
    (∀ k j : Int, 0 ≤ k ∧ k ≤ a → 0 ≤ a * j - b * k ∧ a * j - b * k < a →
      TriangularBoundaryStrip x (x + (a, b) + (c, d)) (x + (k, j))) ∧
    (∀ k j : Int, 0 ≤ k ∧ k ≤ c → 0 ≤ c * j - d * k ∧ c * j - d * k < c →
      TriangularBoundaryStrip x (x + (a, b) + (c, d))
        (x + (a, b) + (k, j))) := by
-- BODY
  have ha : 0 < a := by
    by_contra hh
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    simp [ha0, hb0] at horient
  have hc : 0 < c := by
    by_contra hh
    have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    simp [hc0, hd0] at horient
  have hw := (P3019T1ChamberStripGeometry x (a + c) (b + d)
    (by omega) (by omega)).2.1
  have hsum : x + (a, b) + (c, d) = x + (a + c, b + d) := by
    simp [add_assoc]
  refine ⟨ha, hc, ?_, ?_⟩
  · intro k j hk hh
    have hid : a * (c * j - d * k) = c * (a * j - b * k) + k := by
      linear_combination -k * horient
    have hell0 : 0 ≤ c * j - d * k := by
      nlinarith [mul_nonneg (le_of_lt hc) hh.1]
    have hell1 : c * j - d * k < c + 1 := by
      nlinarith [mul_pos hc (sub_pos.mpr hh.2)]
    rw [hsum, hw]
    simp only [Prod.fst_add, Prod.snd_add, add_sub_cancel_left]
    constructor <;> nlinarith
  · intro k j hk hh
    have hid : c * (a * j - b * k) = a * (c * j - d * k) - k := by
      linear_combination k * horient
    have hq0 : -1 ≤ a * j - b * k := by
      nlinarith [mul_nonneg (le_of_lt ha) hh.1]
    have hq1 : a * j - b * k < a := by
      nlinarith [mul_pos ha (sub_pos.mpr hh.2)]
    have height : (a + c) * (b + j) - (b + d) * (a + k) =
        1 + (a * j - b * k) + (c * j - d * k) := by
      linear_combination -horient
    rw [hsum, hw]
    simp only [Prod.fst_add, Prod.snd_add]
    have hx1 : x.1 + a + k - x.1 = a + k := by omega
    have hx2 : x.2 + b + j - x.2 = b + j := by omega
    rw [hx1, hx2, height]
    constructor <;> omega

end ApollonianSuperharmonic

end
