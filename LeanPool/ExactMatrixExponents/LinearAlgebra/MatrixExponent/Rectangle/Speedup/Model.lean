/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Model

/-! # Parameters of the finite border-rank inequality -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle

/-- The maximum of the quantities in `(i * j) (max (i * k) (j * k))`. -/
def largest (i j k : ℕ) := max (i * j) (max (i * k) (j * k))

/-- Computes the value by the application `Real.exp (exponent F (Real.log i) (Real.log j)
(Real.log k))`. -/
def value (F : Type*) [Field F] (i j k : ℕ) : ℝ :=
  Real.exp (exponent F (Real.log i) (Real.log j) (Real.log k))

/-- The quantity computed by `Real.log (value F i j k) / Real.log ((i : ℝ) * j * k)`. -/
def slope (F : Type*) [Field F] (i j k : ℕ) : ℝ :=
  Real.log (value F i j k) / Real.log ((i : ℝ) * j * k)

/-- The supremum of `{y | ∃ v : ℝ, 2 < v ∧ y = ((v - 1) ^ (3 / 4 : ℝ) - 1) / v}`. -/
def Speedup.cStar : ℝ := sSup {y | ∃ v : ℝ, 2 < v ∧ y = ((v - 1) ^ (3 / 4 : ℝ) - 1) / v}

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle
