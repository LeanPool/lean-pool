/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialSystem

/-! # Rounding errors in the number of integers in a short interval -/

@[expose] public section

namespace NairTenenbaum

theorem shortInterval_card_bounds {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y - 1 ≤ ((shortInterval x y).card : ℝ) ∧ ((shortInterval x y).card : ℝ) ≤ y + 1 := by
  have hfloor : ⌊x⌋₊ ≤ ⌊x + y⌋₊ := Nat.floor_mono (by linarith)
  have HE : ((shortInterval x y).card : ℝ) = (⌊x + y⌋₊ : ℝ) - (⌊x⌋₊ : ℝ) := by
    simp only [shortInterval, Nat.card_Ioc, Nat.cast_sub hfloor]
  rw [HE]
  have Hx := Nat.floor_le hx
  have Hxy := Nat.floor_le (add_nonneg hx hy)
  have Hx' := Nat.lt_floor_add_one x
  have Hxy' := Nat.lt_floor_add_one (x + y)
  constructor <;> linarith

theorem shortInterval_card_le_twice {x y : ℝ} (hx : 0 ≤ x) (hy : 1 ≤ y) :
    ((shortInterval x y).card : ℝ) ≤ 2 * y := by
  have H := (shortInterval_card_bounds hx (by linarith)).2
  linarith

end NairTenenbaum
