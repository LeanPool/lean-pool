/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Blocks
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.Ring.Defs
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassSemiring

/-!
# The semiring of actual finite tensors

Every law is obtained from an explicit coordinate relabeling. The quotient
identifies mutual restriction, not numerical ranks or an abstract tensor model.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.CoefficientTensor
open scoped NNReal

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (ofTensor_add ofTensor_mul add_comm_aux add_assoc_aux zero_add_aux mul_comm_aux
    mul_assoc_aux one_mul_aux zero_mul_aux left_distrib_aux add_mono mul_mono zero_le)

/-- The empty tensor over the coefficient ring. -/
abbrev emptyTensor :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.emptyTensor (K := O)

/-- The unit tensor over the coefficient ring. -/
abbrev unitTensor :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.unitTensor (K := O)

/-- Normalized additive multiplicative monotone quantities on actual tensor
classes. This definition asserts no existence theorem. -/
structure Character where
  /-- The `Character` component of type `TensorClass →+* ℝ≥0`. -/
  toHom : TensorClass →+* ℝ≥0
  monotone' : Monotone toHom

noncomputable instance : CoeFun Character (fun _ => TensorClass → ℝ≥0) := ⟨fun f => f.toHom⟩

@[simp] theorem Character.map_zero (f : Character) : f 0 = 0 := f.toHom.map_zero
@[simp] theorem Character.map_one (f : Character) : f 1 = 1 := f.toHom.map_one
@[simp] theorem Character.map_add (f : Character) (A B : TensorClass) :
    f (A + B) = f A + f B := f.toHom.map_add A B
@[simp] theorem Character.map_mul (f : Character) (A B : TensorClass) :
    f (A * B) = f A * f B := f.toHom.map_mul A B

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass
