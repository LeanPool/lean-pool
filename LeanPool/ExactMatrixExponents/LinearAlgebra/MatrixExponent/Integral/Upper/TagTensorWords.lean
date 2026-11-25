/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Separation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Powers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagWords
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagTensorWords

/-!
# Coefficient tensor words and matched-label restrictions

Tensor powers of a shared-first-leg tensor have one branch for each word.
The regrouping below preserves all coefficients, including the zero
coefficients between different words. Selecting words by an injection is an
actual local restriction. Multiplicativity is then applied to the actual
tensor product represented by each word.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TagTensorWords

export MatrixMultiplicationAllFields.TensorSpectrum.TagTensorWords
  (sharedLabels tensorWord wordBranch joinCoordinates power_shared_pullback
    restricts_power_shared_words ofTensor_shared_words shared_injective_pullback
    restricts_shared_injective restricts_power_shared_selected restricts_power_shared_fiber
    restricts_power_shared_fiber_enumeration headTailCoordinates ofTensor_tensorWord
    map_wordBranch map_wordBranch_of_mem_fiber)

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TagTensorWords
