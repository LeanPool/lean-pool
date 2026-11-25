/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Semiring
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Rank
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassRankOrder

/-!
# Rank bounds and the concrete tensor order

Natural numbers in the quotient semiring are precisely the diagonal tensors.
These lemmas connect ordinary finite decompositions to the order used by states.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.CoefficientTensor

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (ofTensor_zero natCast_eq_ofTensor_natTensor rank_add_le rank_mul_le le_rank_natCast
    rank_eq_zero_iff mul_le_rank_mul)

namespace Character

theorem map_natCast (f : Character) (n : ℕ) : f n = n :=
  TensorSpectrum.TensorClass.Character.map_natCast f n

theorem le_rank (f : Character) (A : TensorClass) : f A ≤ rank A :=
  TensorSpectrum.TensorClass.Character.le_rank f A

end Character

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass
