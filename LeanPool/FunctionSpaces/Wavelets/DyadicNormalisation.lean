/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.ApproximationSpaces.Sequences.Lq
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The normalising factor `2^(j/2)` of dyadic dilations

Haar functions, multiwavelets and Daubechies wavelets of level `j` carry the factor `2^(j/2)`,
which makes the dilation `g ↦ 2^(j/2) g(2^j ·)` an isometry of `L_2`. As a complex number its
square is `2^j` (`ofReal_two_rpow_half_mul_self`), and its extended norm is the dyadic weight
`2^(j/2)` (`enorm_two_rpow_half`).
-/

@[expose] public section

open scoped ENNReal

/-- **The square of the normalising factor**: `2^(j/2) · 2^(j/2) = 2^j` for every `j ∈ ℕ`, as
complex numbers (Mathlib's `Real.rpow_add` and `add_halves`). -/
theorem ofReal_two_rpow_half_mul_self (j : ℕ) :
    (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) * (((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ) = (2 : ℂ) ^ j := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add two_pos, add_halves, Real.rpow_natCast]
  push_cast
  rfl

/-- **The normalising factor in extended norm**: `‖2^(j/2)‖ = 2^(j/2)` for every `j ∈ ℕ`, written
as the dyadic weight `ENNReal.dyadicWeight (1/2) j`. -/
theorem enorm_two_rpow_half (j : ℕ) :
    ‖(((2 : ℝ) ^ ((j : ℝ) / 2) : ℝ) : ℂ)‖ₑ = ENNReal.dyadicWeight (1 / 2) j := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    ← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat, ENNReal.dyadicWeight, mul_one_div]
