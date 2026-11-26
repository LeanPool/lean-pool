/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Nodes
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.LocalTensor
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

/-! # Coefficient tensor for the integral upper bound -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

/-- Computes the matrix tensor by the application `Tensor.matrixCoefficients (Fin a) (Fin b)
(Fin c)`. -/
def matrixTensor (a b c : ℕ) :
    Tensor O (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
