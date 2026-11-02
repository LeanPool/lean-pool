/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyAverageReductions
public import LeanPool.NairTenenbaum.Hooley.HooleyWeightedMean

/-! # Corollary 5: averages of floor differences in short intervals

The `sqrt(2)+o(1)` exponent is expressed by quantifying every larger real
coefficient. Both the cutoff and the bound constant are uniform in `D`.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial

/-- The statement of Corollary 5, with the scope recorded in the source alignment. -/
def CorollaryFive : Prop :=
  ∀ ε η : ℝ, 0 < ε → ε < 1 → Real.sqrt 2 < η →
    ∃ x₀ C : ℝ, 1 < x₀ ∧ 0 < C ∧ ∀ D x y : ℝ,
      1 ≤ D → x₀ < x → x ^ ε ≤ y → y ≤ x →
        dyadicFloorSum D x y ≤ C * (y * hooleySubexponential η x)

theorem corollaryFive : CorollaryFive := by
  intro ε η hε _ hη
  obtain ⟨x₁, A, _, hA, HA⟩ := exists_dyadicFloorSum_root_bound hε
  obtain ⟨x₂, B, hx₂, hB, HB⟩ := exists_hooleyRootSum_X_sharp_bound hη
  refine ⟨max x₁ x₂, A * B, hx₂.trans_le (le_max_right _ _), mul_pos hA hB,
    fun D x y hD hx hy hyx => ?_⟩
  have hx₁ : x₁ < x := (le_max_left _ _).trans_lt hx
  have hx₂' : x₂ < x := (le_max_right _ _).trans_lt hx
  have hxpos : 1 < x := hx₂.trans hx₂'
  have hl : 0 < Real.log x := Real.log_pos hxpos
  have hy₀ : 0 ≤ y := (Real.rpow_nonneg (by linarith : 0 ≤ x) _).trans hy
  calc
    _ ≤ A * (y / Real.log x * hooleyRootSum (X : ℤ[X]) 1 x) :=
      HA D x y (by linarith) hx₁ hy hyx
    _ ≤ A * (y / Real.log x * (B * (Real.log x * hooleySubexponential η x))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (HB x hx₂') (div_nonneg hy₀ hl.le)) hA.le
    _ = _ := by field_simp

end NairTenenbaum
