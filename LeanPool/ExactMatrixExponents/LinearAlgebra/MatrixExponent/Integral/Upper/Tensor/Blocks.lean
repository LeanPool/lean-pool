/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Base
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.Blocks

/-!
# Heterogeneous direct sums and restrictions

The two summands retain separate coordinates on every leg. Cross coefficients
are zero, and block diagonal local matrices give actual restriction witnesses.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.CoefficientTensor

export MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor
  (blockSum blockMatrix blockSum_inl blockSum_inr restrict_blockSum pullback_blockSum)

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.Restricts
  (blockSum product)

end Restricts

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.CoefficientTensor
