/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import Mathlib.Basic.Real.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# Scalar estimates for elliptic energy and variational arguments

These bounds isolate polynomial arithmetic from the function spaces and coefficient operators
appearing in their applications.
-/

@[expose] public section

namespace EllipticPdes.Analysis

/-- The quadratic variation of a Rayleigh bound is nonnegative at a minimizer. -/
lemma quadratic_nonneg_of_rayleigh_bound {lam a b c d t : ℝ}
    (h : lam * (1 + 2 * t * c + t ^ 2 * d) ≤ lam + 2 * t * a + t ^ 2 * b) :
    0 ≤ 2 * t * (a - lam * c) + t ^ 2 * (b - lam * d) := by
  nlinarith only [h]

/-- A triangular bound on nonnegative quantities gives a two-square bound. -/
lemma square_le_twice_squares_of_le_add {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b + c) :
    a ^ 2 ≤ 2 * b ^ 2 + 2 * c ^ 2 := by
  nlinarith only [ha, hb, hc, h, sq_nonneg (b - c)]

/-- Nonnegative coefficients combine separate squared data and function bounds. -/
lemma energy_le_combined_squares {energy a b c datum value : ℝ}
    (hc : 0 ≤ a + b + c)
    (h : energy ≤ 1 / 2 * datum ^ 2 + a * value ^ 2 + b * value ^ 2 + c * value ^ 2) :
    energy ≤ (1 / 2 + a + b + c) * (datum ^ 2 + value ^ 2) := by
  nlinarith only [h, mul_nonneg hc (sq_nonneg datum), sq_nonneg value]

/-- Two weighted nonnegative quantities are bounded using the sum of their coefficients. -/
lemma weighted_pair_le_sum_mul_add {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    a * x + b * y ≤ (a + b) * (x + y) := by
  nlinarith only [mul_nonneg ha hy, mul_nonneg hb hx]

end EllipticPdes.Analysis
