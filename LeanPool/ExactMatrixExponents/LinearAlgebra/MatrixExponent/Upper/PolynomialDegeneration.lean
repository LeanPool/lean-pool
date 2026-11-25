/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialTensors
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensorRestrictionComposition
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.WeightedPolynomials

/-!
# Diagonal weight degenerations

The terms of weight zero form the limiting tensor. Positive weights
contribute higher polynomial coefficients, and negative weights occur
only at zero entries.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper

export MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors
  (weightedLimit weightedFamily weightedFamily_zero restrict_diagonal)

variable {X Y Z : Type*}

/-- At every nonzero parameter, the family is witnessed by actual
local substitutions: the diagonal entries are the respective integer powers. -/
theorem weightedFamily_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor Coeff X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    {t : Coeff} (ht : t ≠ 0) :
    weightedFamily T wx wy wz t ∈ LocalTensor.orbit T :=
  TensorSpectrum.PolynomialTensors.weightedFamily_mem_restrictionOrbit T wx wy wz h t
    (fun n => t ^ n) (fun i j => zpow_add₀ ht i j) (fun n => zpow_natCast t n)

end MatrixMultiplicationAllFields.MatrixExponent.Upper
