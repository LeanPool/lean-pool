/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.RankOrder
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassPowers

/-!
# Tensor powers and full repeated direct sums in the quotient

These bridges preserve the actual coefficient tensors used by interpolation.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (ofTensor_power ofTensor_directSum_const)

namespace Character

theorem map_power_tensor (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor Coeff X Y Z) (n : ℕ) :
    f (ofTensor (Tensor.power T n)) = (f (ofTensor T)) ^ n :=
  TensorSpectrum.TensorClass.Character.map_power_tensor f T n

theorem map_directSum_const (f : Character) {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor Coeff X Y Z) (n : ℕ) :
    f (ofTensor (Tensor.directSum (fun _ : Fin n => T))) =
      (n : ℝ≥0) * f (ofTensor T) :=
  TensorSpectrum.TensorClass.Character.map_directSum_const f T n

end Character

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
