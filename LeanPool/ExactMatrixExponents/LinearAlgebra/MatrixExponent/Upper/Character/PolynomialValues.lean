/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.TagFinite
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialTensor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.CharacterDegeneration

/-!
# Positivity and rank bounds for polynomial character values

The constant input monomials witness nonvanishing.  The upper bound uses the
actual evaluation/interpolation rank decomposition of ordinary convolution.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper

namespace TensorClass

theorem Character.polynomial_value_pos (f : Character) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < (f (ofTensor (polynomialTensor a b)) : ℝ) :=
  TensorSpectrum.TensorClass.Character.polynomial_value_pos f a b ha hb

theorem Character.polynomial_value_le (f : Character) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (f (ofTensor (polynomialTensor a b)) : ℝ) ≤ (a : ℝ) + (b : ℝ) - 1 :=
  TensorSpectrum.TensorClass.Character.polynomial_value_le_of_rankAtMost
    f a b ha hb (polynomialTensor_rankAtMost a b)

end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Upper
