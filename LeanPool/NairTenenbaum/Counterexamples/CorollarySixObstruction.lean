/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Counterexamples.ConstantCoordinate
public import LeanPool.NairTenenbaum.Results.CorollarySix

/-! # Why Corollary 6 needs a nonconstant restricted coordinate

Take `Q₁=X`, `Q₂=1`, and `F=1`. The total polynomial has degree one,
height one, and no fixed prime divisor. The smoothness condition on `Q₂`
is vacuous. The following counterexample uses the admissible parameters
`ε=1/16`, `δ=1`, `κ=log(2)/16`, and `z=2`.
-/

@[expose] public section

namespace NairTenenbaum

theorem constantCoordinateSystem_height : polynomialHeight constantCoordinateSystem.total
    = 1 := by
  rw [constantCoordinateSystem_total]
  simp [polynomialHeight]

/-- Every proposed uniform constant fails for the constant restricted
coordinate, even with the original interval and smoothness ranges. -/
theorem constant_coordinate_smooth_bound_fails (c₀ C : ℝ) (hC : 0 ≤ C) :
    ∃ x : ℝ, 2 ≤ x ∧ c₀ < x ∧ x ^ (1 / 4 : ℝ) ≤ x ∧
      (2 : ℝ) ^ ((Real.log 2 / 16) / (2 * (1 / 16))) ≤ 2 ∧
      C * Real.exp (-(Real.log 2 / 16) * Real.log x / Real.log 2) *
        mainTerm constantCoordinateSystem (fun _ => 1) x x <
          smoothShortSum constantCoordinateSystem.Q (fun _ => 1) 1 x x 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max c₀ (max C 2))
  have hNc : c₀ < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNC : C < (N : ℝ) := (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hN)
  have hN₂ : (2 : ℝ) < N := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hN)
  have hN₀ : (0 : ℝ) < N := by linarith
  have hNpow : (N : ℝ) ≤ (N : ℝ) ^ (16 : ℕ) := by
    exact le_self_pow₀ (by linarith : (1 : ℝ) ≤ N) (by norm_num : 16 ≠ 0)
  let x : ℝ := (N : ℝ) ^ (16 : ℕ)
  have hx₂ : 2 ≤ x := hN₂.le.trans hNpow
  have hx₀ : 0 < x := by dsimp [x]; positivity
  have hlog₂ : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have Hsave : Real.exp (-(Real.log 2 / 16) * Real.log x / Real.log 2) = (N : ℝ)⁻¹ := by
    dsimp [x]
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have Heq : -(Real.log 2 / 16) * (16 * Real.log N) / Real.log 2 = -Real.log N := by
      field_simp
    rw [Heq, Real.exp_neg, Real.exp_log hN₀]
  refine ⟨x, hx₂, hNc.trans_le hNpow, ?_, ?_, ?_⟩
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ x) (by norm_num : (1 / 4 : ℝ) ≤ 1)
  · have he : (Real.log 2 / 16) / (2 * (1 / 16)) ≤ 1 := by
      norm_num
      linarith [Real.log_two_lt_d9]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  · have Hsum : smoothShortSum constantCoordinateSystem.Q (fun _ => 1) 1 x x 2 = x := by
      have H := constantCoordinateSystem_smooth_sum (N ^ 16) 2
      rw [Nat.cast_pow] at H
      exact H
    rw [Hsum, Hsave]
    have Hmain := constantCoordinateSystem_mainTerm_one_le (x := x) hx₀.le
    calc
      _ ≤ (C * (N : ℝ)⁻¹) * x := mul_le_mul_of_nonneg_left Hmain (by positivity)
      _ < 1 * x := mul_lt_mul_of_pos_right (by
        rw [← div_eq_mul_inv]
        exact (div_lt_one hN₀).mpr hNC) hx₀
      _ = _ := one_mul x

end NairTenenbaum
