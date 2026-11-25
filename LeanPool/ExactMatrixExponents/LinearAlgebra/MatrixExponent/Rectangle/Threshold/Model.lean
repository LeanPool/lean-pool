/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.FiniteModel

/-! # Scaling the inner dimension at the harmonic threshold -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Threshold

/-- The quantity computed by `⌈a * (n : ℝ) ^ (x * y)⌉₊`. -/
def width (n : ℕ) (x y a : ℝ) := ⌈a * (n : ℝ) ^ (x * y)⌉₊

/-- The quantity computed by `Real.exp (-u) * (max (b + C * u) 0) ^ 2 / 4`. -/
def gain (b C u : ℝ) := Real.exp (-u) * (max (b + C * u) 0) ^ 2 / 4

/-- Returns `C ^ 2 * Real.exp (b / C - 2)` when `b ≤ 2 * C` holds, and `b ^ 2 / 4` otherwise. -/
def optimum (b C : ℝ) := if b ≤ 2 * C then C ^ 2 * Real.exp (b / C - 2) else b ^ 2 / 4

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Threshold
