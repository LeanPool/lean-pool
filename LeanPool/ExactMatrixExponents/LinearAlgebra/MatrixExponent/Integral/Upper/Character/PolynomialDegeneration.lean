/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Degeneration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialFiltrationFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialSectorFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialCharacterBounds

/-!
# Character bounds from the two explicit polynomial families

Both inequalities use the actual finite-degree restriction witnesses.  In
the determinant case the two-dimensional pairing is explicitly charged.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass

theorem binaryDotTensor_class : ofTensor binaryDotTensor = dotX 2 :=
  TensorSpectrum.TensorClass.binaryDotTensor_class (K := O)

theorem Character.determinant_graded_le (f : Character) (a b : ℕ) :
    (f (ofTensor (determinantGradedTensor a b)) : ℝ) ≤
      (2 : ℝ) ^ f.pX * (f (ofTensor (polynomialTensor (a + 1) (b + 2))) : ℝ) := by
  have h := f.polynomial_constant_le
    (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor)
    (determinantGradedTensor a b) (determinantPolynomialFamily a b) 1
    (fun i y z => congrFun (congrFun (congrFun
      (determinantPolynomialFamily_coeff_zero a b) i) y) z)
    (determinantPolynomialFamily_degree_le a b)
    (fun t ht => determinantPolynomialFamily_eval_mem_restrictionOrbit a b ht)
  exact TensorSpectrum.TensorClass.Character.determinant_graded_le f a b h

theorem Character.tripling_graded_le (f : Character) (a h : ℕ)
    (ha : 1 ≤ a) (hh : 1 ≤ h) :
    (f (ofTensor (triplingSectorTensor a h)) : ℝ) ≤
      (f (ofTensor (polynomialTensor a (3 * h + a - 1))) : ℝ) := by
  apply TensorSpectrum.TensorClass.Character.tripling_graded_le f a h
  exact Separation.polynomial_power_mem_restrictionOrbit
    (polynomialTensor a (triplingWidth a h)) (triplingSectorTensor a h)
    (triplingPolynomialFamily a h ha hh) 1
    (triplingPolynomialFamily_coeff_zero a h ha hh)
    (triplingPolynomialFamily_degree_le a h ha hh)
    (fun t ht => triplingPolynomialFamily_eval_mem_restrictionOrbit a h ha hh ht)

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass
