/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Interpolation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialTensors
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.WeightedPolynomials
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition

/-! # Polynomial degenerations of integral coefficient tensors -/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper

export MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors
  (weightedLimit weightedFamily weightedFamily_zero restrict_diagonal)

variable {X Y Z : Type*}

/-- At every nonzero parameter, the family is witnessed by actual
local substitutions: the diagonal entries are the respective integer powers. -/
theorem weightedFamily_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor O X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    {t : O} (ht : IsUnit t) :
    weightedFamily T wx wy wz t ∈ LocalTensor.orbit T :=
  TensorSpectrum.PolynomialTensors.weightedFamily_mem_restrictionOrbit T wx wy wz h t
    (fun n => t ^ n) (fun i j => upow_add ht i j) (fun n => upow_nat t n)

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
