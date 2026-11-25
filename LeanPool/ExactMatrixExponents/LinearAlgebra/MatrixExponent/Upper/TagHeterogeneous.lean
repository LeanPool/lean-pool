/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Separation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Base
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialSectors
public import Mathlib.Tactic.FinCases
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagHeterogeneous

/-!
# Heterogeneous shared-first-leg tensors

Padding a branch adds only zero coordinates. The extra uniform labels used by
the separation construction are removed by actual independent local maps.
The first leg is shared throughout; no direct-sum additivity is used here.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TagHeterogeneous

export MatrixMultiplicationAllFields.TensorSpectrum.TagHeterogeneous
  (sharedTwo padLeft padRight ofTensor_padLeft ofTensor_padRight maskedFamily
    ofTensor_shared_maskedFamily twoLabel twoFamily twoFamily_eq_maskedFamily
    ofTensor_shared_twoFamily ofTensor_twoFamily sharedThree threeLabel threeFamily
    threeFamily_eq_maskedFamily ofTensor_shared_threeFamily ofTensor_threeFamily)

/-- The polynomial branch with reversed first coordinate. -/
abbrev triplingMiddleTensor :=
  TensorSpectrum.TagHeterogeneous.triplingMiddleTensor (K := Coeff)

/-- The heterogeneous tensor represents the three polynomial sectors. -/
theorem triplingSectorTensor_eq_sharedThree (a h : ℕ) :
    triplingSectorTensor a h = sharedThree (polynomialTensor a h)
      (triplingMiddleTensor a h) (polynomialTensor a h) :=
  TensorSpectrum.TagHeterogeneous.triplingSectorTensor_eq_sharedThree a h

/-- The three sectors and their uniform-label tensor have the same restriction class. -/
theorem ofTensor_tripling_uniform (a h : ℕ) :
    TensorClass.ofTensor (Separation.shared
      (threeFamily (polynomialTensor a h) (triplingMiddleTensor a h)
        (polynomialTensor a h))) = TensorClass.ofTensor (triplingSectorTensor a h) :=
  TensorSpectrum.TagHeterogeneous.ofTensor_tripling_uniform a h

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TagHeterogeneous
