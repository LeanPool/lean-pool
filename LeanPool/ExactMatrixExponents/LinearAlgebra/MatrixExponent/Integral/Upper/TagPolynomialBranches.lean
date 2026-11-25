/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.TagHeterogeneous
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialFiltration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Permutations
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.PolynomialValues
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagPolynomialBranches

/-!
# Polynomial branches in the heterogeneous tag construction

The determinant branches retain their actual output coordinates; finite
coordinate equivalences identify their classes with polynomial multiplication.
The middle tripling branch is a last-two-leg swap followed by the stated
invertible reversal of the shared first coordinate.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TagHeterogeneous

/-- The specialization of `determinantQuotientTensor` to these coefficients. -/
abbrev determinantQuotientTensor :=
  TensorSpectrum.TagHeterogeneous.determinantQuotientTensor (K := O)

/-- The specialization of `determinantKernelTensor` to these coefficients. -/
abbrev determinantKernelTensor :=
  TensorSpectrum.TagHeterogeneous.determinantKernelTensor (K := O)

export MatrixMultiplicationAllFields.TensorSpectrum.TagHeterogeneous
  (triplingReverseEquiv)

theorem determinantGradedTensor_eq_sharedTwo (a b : ℕ) :
    determinantGradedTensor a b =
      sharedTwo (determinantQuotientTensor a b) (determinantKernelTensor a b) :=
  TensorSpectrum.TagHeterogeneous.determinantGradedTensor_eq_sharedTwo a b

theorem ofTensor_determinantQuotient (a b : ℕ) :
    TensorClass.ofTensor (determinantQuotientTensor a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)) :=
  TensorSpectrum.TagHeterogeneous.ofTensor_determinantQuotient a b

theorem ofTensor_determinantKernel (a b : ℕ) :
    TensorClass.ofTensor (determinantKernelTensor a b) =
      TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1)) :=
  TensorSpectrum.TagHeterogeneous.ofTensor_determinantKernel a b

/-- The uniform separation input is the whole graded determinant tensor. -/
theorem ofTensor_determinant_uniform (a b : ℕ) :
    TensorClass.ofTensor (Separation.shared
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b))) =
      TensorClass.ofTensor (determinantGradedTensor a b) :=
  TensorSpectrum.TagHeterogeneous.ofTensor_determinant_uniform a b

/-- Both original polynomial branches survive zero padding exactly. -/
theorem ofTensor_determinant_family (a b : ℕ) (j : Fin 2) :
    TensorClass.ofTensor
      (twoFamily (determinantQuotientTensor a b) (determinantKernelTensor a b) j) =
      ![TensorClass.ofTensor (polynomialTensor (a + 1) (b + 3)),
        TensorClass.ofTensor (polynomialTensor (a + 1) (b + 1))] j :=
  TensorSpectrum.TagHeterogeneous.ofTensor_determinant_family a b j

/-- The middle branch is evaluated using the permuted character. Its
first-coordinate reversal is removed only by an invertible local map. -/
theorem ofTensor_triplingMiddle (a h : ℕ) :
    TensorClass.ofTensor (triplingMiddleTensor a h) =
      TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)) :=
  TensorSpectrum.TagHeterogeneous.ofTensor_triplingMiddle a h

theorem ofTensor_tripling_family (a h : ℕ) (j : Fin 3) :
    TensorClass.ofTensor
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h) j) =
      ![TensorClass.ofTensor (polynomialTensor a h),
        TensorClass.swapYZ (TensorClass.ofTensor (polynomialTensor a h)),
        TensorClass.ofTensor (polynomialTensor a h)] j :=
  TensorSpectrum.TagHeterogeneous.ofTensor_tripling_family a h j

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TagHeterogeneous
