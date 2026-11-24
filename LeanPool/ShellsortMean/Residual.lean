/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! Signed arithmetic interfaces for the two-pass residual proof.
These theorems do not yet identify this expression with a Shellsort chain count.
-/
@[expose] public section

namespace Shellsort

/-- The phase residual, with subtraction in integers, never truncated naturals. -/
def phaseResidual (g a y : ℕ) : ℤ :=
  (g : ℤ) * (if a < y % g then 1 else 0) - (y % g : ℤ)

theorem phaseResidual_bounds (g a y : ℕ) (hg : 0 < g) (ha : a < g) :
    -(a : ℤ) ≤ phaseResidual g a y ∧
      phaseResidual g a y ≤ (g : ℤ) - 1 - a := by
  have hv := Nat.mod_lt y hg
  unfold phaseResidual
  split_ifs with h
  · simp only [mul_one]
    constructor <;> omega
  · simp only [mul_zero, zero_sub]
    constructor <;> omega

theorem phaseResidual_owner (g y : ℕ) :
    phaseResidual g (y % g) y = -(y % g : ℤ) := by
  simp [phaseResidual]

theorem phaseResidual_owner_min (g a y : ℕ) (hg : 0 < g) (ha : a < g) :
    -(a : ℤ) ≤ phaseResidual g a y :=
  (phaseResidual_bounds g a y hg ha).1

/-- The complete-prefix mean and a one-sided owner correction imply the
uniform absolute mean bound. `reference` is the summed reference mean. -/
theorem owner_mean_bound (g j reference correction : ℝ)
    (_ : 1 ≤ g)
    (href0 : 0 ≤ j + reference) (href1 : j + reference ≤ g - 1)
    (hc0 : -(g - 1) ≤ correction) (hc1 : correction ≤ 0) :
    |j + reference + correction| ≤ g - 1 := by
  rw [abs_le]
  constructor <;> linarith

end Shellsort
