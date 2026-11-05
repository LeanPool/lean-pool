/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.SummatoryFractionalMoment

/-! # Linear convolution error from a power-saving summatory estimate -/

@[expose] public section

namespace NairTenenbaum

open Finset ArithmeticFunction Real

theorem arithmeticSummatory_mul_finite (a g : ArithmeticFunction ℝ) (x : ℝ) :
    arithmeticSummatory (g * a : ArithmeticFunction ℝ) x =
      ∑ d ∈ Icc 1 ⌊x⌋₊, g d * arithmeticSummatory a (x / d) := by
  unfold arithmeticSummatory
  simp_rw [ArithmeticFunction.mul_apply, Nat.floor_div_natCast]
  rw [sum_divisorsAntidiagonal_eq_hyperbola (fun d e => g d * a e)]
  simp_rw [mul_sum]

theorem arithmeticSummatory_convolution_power_error {a g : ArithmeticFunction ℝ}
    (hg : ∀ n, 0 ≤ g n) {κ E C θ x : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C)
    (ha : ∀ t : ℝ, 1 ≤ t → |arithmeticSummatory a t - κ * t| ≤ E * t ^ θ)
    (hbound : ∀ t : ℝ, 1 ≤ t → arithmeticSummatory g t ≤ C * t)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hx : 1 ≤ x) :
    |arithmeticSummatory (g * a : ArithmeticFunction ℝ) x -
      κ * x * arithmeticSummatory (fun n => g n / n) x| ≤ E * C / (1 - θ) * x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heq : arithmeticSummatory (g * a : ArithmeticFunction ℝ) x -
      κ * x * arithmeticSummatory (fun n => g n / n) x =
      ∑ d ∈ Icc 1 ⌊x⌋₊, g d * (arithmeticSummatory a (x / d) - κ * (x / d)) := by
    rw [arithmeticSummatory_mul_finite]
    unfold arithmeticSummatory
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro d _
    ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Icc 1 ⌊x⌋₊, |g d * (arithmeticSummatory a (x / d) - κ * (x / d))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 ⌊x⌋₊, E * x ^ θ * (g d / (d : ℝ) ^ θ) := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (mem_Icc.mp hd).1
      have hdx : (d : ℝ) ≤ x := (Nat.cast_le.mpr (mem_Icc.mp hd).2).trans (Nat.floor_le hx0.le)
      have hratio : 1 ≤ x / d := (le_div_iff₀ hd0).mpr (by simpa using hdx)
      rw [abs_mul, abs_of_nonneg (hg d)]
      calc
        _ ≤ g d * (E * (x / d) ^ θ) := mul_le_mul_of_nonneg_left (ha _ hratio) (hg d)
        _ = _ := by rw [Real.div_rpow hx0.le hd0.le]; ring
    _ = E * x ^ θ * arithmeticSummatory (fun n => g n / (n : ℝ) ^ θ) x := by
      rw [arithmeticSummatory, mul_sum]
    _ ≤ E * x ^ θ * (C / (1 - θ) * x ^ (1 - θ)) :=
      mul_le_mul_of_nonneg_left
        (arithmeticSummatory_rpow_le g.map_zero hg hC hbound hθ hθ1 hx)
        (mul_nonneg hE (Real.rpow_nonneg hx0.le _))
    _ = _ := by
      calc
        _ = E * C / (1 - θ) * (x ^ θ * x ^ (1 - θ)) := by ring
        _ = _ := by rw [← Real.rpow_add hx0, show θ + (1 - θ) = 1 by ring, Real.rpow_one]

end NairTenenbaum
