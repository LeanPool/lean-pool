/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassSemiring
public import Mathlib.Basic.NNReal.Defs

/-!
# Characters on tensor classes

Characters take values in the nonnegative reals and preserve order and the semiring operations.
-/

@[expose] public section

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.TensorSpectrum.TensorClass

variable {K : Type*} [CommSemiring K]

/-- A semiring homomorphism to nonnegative reals that preserves the local restriction order. -/
structure Character (K : Type*) [CommSemiring K] where
  /-- The underlying semiring homomorphism. -/
  toHom : (TensorClass K) →+* ℝ≥0
  monotone' : Monotone toHom

noncomputable instance : CoeFun (Character K) (fun _ => TensorClass K → ℝ≥0) := ⟨fun f => f.toHom⟩

@[simp] theorem Character.map_zero (f : (Character K)) : f 0 = 0 := f.toHom.map_zero
@[simp] theorem Character.map_one (f : (Character K)) : f 1 = 1 := f.toHom.map_one
@[simp] theorem Character.map_add (f : (Character K)) (A B : (TensorClass K)) :
    f (A + B) = f A + f B := f.toHom.map_add A B
@[simp] theorem Character.map_mul (f : (Character K)) (A B : (TensorClass K)) :
    f (A * B) = f A * f B := f.toHom.map_mul A B

end MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
