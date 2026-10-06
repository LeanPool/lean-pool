/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.StretchingBounds

/-!
# Polar REq Zero

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- `polarR x = 0` exactly when the point lies on the vertical axis: `x 0 = 0` and `x 1 = 0`. -/
theorem polarR_eq_zero_iff (x : Vec3) : polarR x = 0 ↔ x 0 = 0 ∧ x 1 = 0 := by
  unfold polarR
  rw [Real.sqrt_eq_zero']
  constructor
  · intro h
    have hsum : x 0 ^ 2 + x 1 ^ 2 = 0 := by
      have hnonneg : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith only [sq_nonneg (x 0), sq_nonneg (x 1), h, hnonneg]
    have h0sq : x 0 ^ 2 = 0 := by
      nlinarith only [sq_nonneg (x 1), hsum]
    have h1sq : x 1 ^ 2 = 0 := by
      nlinarith only [sq_nonneg (x 0), hsum]
    exact ⟨sq_eq_zero_iff.mp h0sq, sq_eq_zero_iff.mp h1sq⟩
  · intro ⟨h0, h1⟩
    rw [h0, h1]
    simp

end CIV
