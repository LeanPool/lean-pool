/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Powers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassDirectSum

/-!
# Character values of full direct sums

Every summand has independent coordinates on all three legs.  This file does
not apply additivity to a tensor whose first leg is shared.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass (ofTensor_directSum_fin)

theorem Character.map_directSum_fin (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (n : ℕ)
    (A : Fin n → Tensor Coeff X Y Z) :
    f (ofTensor (Tensor.directSum A)) = ∑ i, f (ofTensor (A i)) :=
  TensorSpectrum.TensorClass.Character.map_directSum_fin f n A

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
