/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Semiring
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialTensor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.Dots
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Tactic.FinCases
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassPermutations

/-!
# Permuting the three actual tensor legs

The two adjacent swaps act on coefficient arrays and on their actual local
restriction witnesses. Their quotient actions preserve the semiring operations.
The six induced characters therefore remain normalized restriction-monotone
characters; their six values form a multiset invariant under either swap.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper
namespace CoefficientTensor

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor
  (swapXY swapYZ swapXY_blockSum swapYZ_blockSum swapXY_product swapYZ_product)

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.Restricts
  (swapXY swapYZ)

end Restricts
end CoefficientTensor

namespace TensorRep

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep
  (swapXY swapYZ)

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.Restricts
  (swapXY swapYZ)

end Restricts
end TensorRep

namespace TensorClass

/-- The specialization of `swapYZ` to these coefficients. -/
abbrev swapYZ :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.swapYZ (K := Coeff)

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (swapXY_ofTensor swapYZ_ofTensor swapXY_swapXY swapYZ_swapYZ swap_braid swapXY_add swapYZ_add
    swapXY_mul swapYZ_mul permuteSwapXY permuteSwapYZ permute_swapXY permute_swapYZ)

namespace Character

/-- The specialization of `permuted` to this coefficient ring. -/
abbrev permuted (f : Character) (i : Fin 6) : Character :=
  TensorSpectrum.TensorClass.Character.permuted f i

end Character
end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Upper
