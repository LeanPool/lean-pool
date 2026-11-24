/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Std

/-! Integer arithmetic of the seed-one gap sequence with multiplier 107/50.
The index here is zero-based, with gaps 1, 4, 10, 23, ... . -/

@[expose] public section

namespace Shellsort.Actual214

/-- The next center after (h) in the integer gap recurrence. -/
def nextGap (h : Nat) : Nat := (107 * h + 94) / 50

/-- The gap center at a given index, starting at one. -/
def gap : Nat → Nat
  | 0 => 1
  | j + 1 => nextGap (gap j)

/-- Multiplying the exact floor recurrence by 50 leaves a positive error. -/
theorem scaled_next_bounds (h : Nat) :
    107 * h + 45 ≤ 50 * nextGap h ∧ 50 * nextGap h ≤ 107 * h + 94 := by
  unfold nextGap
  omega

/-- Thus the natural-number subtraction equals the ordinary rounding error. -/
theorem residual_bounds (h : Nat) :
    45 ≤ 50 * nextGap h - 107 * h ∧ 50 * nextGap h - 107 * h ≤ 94 := by
  obtain ⟨hl, hu⟩ := scaled_next_bounds h
  omega

theorem gcd_dvd_residual (h : Nat) :
    Nat.gcd h (nextGap h) ∣ 50 * nextGap h - 107 * h :=
  Nat.dvd_sub (Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_right _ _) 50)
    (Nat.dvd_mul_left_of_dvd (Nat.gcd_dvd_left _ _) 107)

theorem gcd_next_le (h : Nat) : Nat.gcd h (nextGap h) ≤ 94 := by
  obtain ⟨hl, hu⟩ := residual_bounds h
  exact Nat.le_trans (Nat.le_of_dvd (by omega) (gcd_dvd_residual h)) hu

theorem adjacent_gap_gcd_le (j : Nat) : Nat.gcd (gap j) (gap (j + 1)) ≤ 94 :=
  gcd_next_le (gap j)

end Shellsort.Actual214
