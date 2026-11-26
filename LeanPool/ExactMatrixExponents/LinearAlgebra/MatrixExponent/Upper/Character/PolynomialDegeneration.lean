/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.Degeneration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.DotsPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialFiltrationFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialSectorFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialCharacterBounds

/-!
# Character bounds from the two explicit polynomial families

Both inequalities use the actual finite-degree restriction witnesses.  In
the determinant case the two-dimensional pairing is explicitly charged.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

theorem binaryDotTensor_class : ofTensor binaryDotTensor = dotX 2 :=
  TensorSpectrum.TensorClass.binaryDotTensor_class (K := Coeff)

theorem Character.determinant_graded_le (f : Character) (a b : ℕ) :
    (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) :=
  TensorSpectrum.TensorClass.Character.determinant_graded_le_of_evaluation f
    (node := fun t : Coeff => t ≠ 0) f.polynomial_constant_le a b
    (fun _ ht => determinantPolynomialFamily_eval_mem_restrictionOrbit a b ht)

theorem Character.tripling_graded_le (f : Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) :
    (f (ofTensor (triplingSectorTensor a h)) : ℝ) ≤
      (f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ) :=
  TensorSpectrum.TensorClass.Character.tripling_graded_le f
    (node := fun t : Coeff => t ≠ 0) f.polynomial_constant_le a h ha hh
    (fun _ ht => triplingPolynomialFamily_eval_mem_restrictionOrbit a h ha hh ht)

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
