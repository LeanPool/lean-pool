/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Blocks
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.Ring.Defs
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassSemiring
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassCharacter

/-!
# The semiring of actual finite tensors

Every law is obtained from an explicit coordinate relabeling. The quotient
identifies mutual restriction, not numerical ranks or an abstract tensor model.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent.Upper.CoefficientTensor
open scoped NNReal

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (ofTensor_add ofTensor_mul add_comm_aux add_assoc_aux zero_add_aux mul_comm_aux
    mul_assoc_aux one_mul_aux zero_mul_aux left_distrib_aux add_mono mul_mono zero_le)

/-- The empty tensor over the coefficient ring. -/
abbrev emptyTensor :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.emptyTensor (K := Coeff)

/-- The unit tensor over the coefficient ring. -/
abbrev unitTensor :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.unitTensor (K := Coeff)

/-- An order-preserving semiring homomorphism on these tensor classes. -/
abbrev Character := MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.Character Coeff

namespace Character

/-- The semiring homomorphism underlying the character. -/
abbrev toHom (f : Character) : TensorClass →+* ℝ≥0 :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.Character.toHom f

/-- Characters preserve the restriction order. -/
theorem monotone' (f : Character) : Monotone f.toHom :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.Character.monotone' f

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.Character
  (map_zero map_one map_add map_mul)

end Character

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
