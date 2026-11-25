/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.FieldFormula
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.UpperBound

/-! # The division-free exponent over nonzero commutative rings -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral

theorem exponent_eq (A : Type*) [CommRing A] [Nontrivial A] {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent A a b c = Rectangle.U a b c :=
  of_fields A ha hb hc (fun F _ => Rectangle.exponent_eq F ha hb hc)

theorem square_exponent (A : Type*) [CommRing A] [Nontrivial A] : exponent A 1 1 1 = 9 / 4 := by
  rw [exponent_eq A zero_le_one zero_le_one zero_le_one]
  norm_num [Rectangle.U, Rectangle.benchmark]

end MatrixMultiplicationAllFields.MatrixExponent.Integral
