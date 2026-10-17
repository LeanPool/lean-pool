/-
Copyright (c) 2026 Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeroen Zuiddam
-/
module

/-
Copyright 2026 Jeroen Zuiddam. Licensed under the Apache License, Version 2.0 (see LICENSE).
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The matrix multiplication tensor over an arbitrary coefficient semiring

`Tensor.matrixMultiplication` is stated over `ℂ`; the all-fields development
uses this field-generic copy, which is definitionally the same tensor.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation.Tensor

/-- The `⟨a,b,c⟩` matrix multiplication tensor over an arbitrary commutative
semiring (the field-generic form of `Tensor.matrixMultiplication`). -/
def matMul (K : Type*) [CommSemiring K] (a b c : ℕ) :
    Tensor K (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  fun x y z => if x.2 = y.1 ∧ y.2 = z.1 ∧ z.2 = x.1 then 1 else 0

theorem matMul_eq_matrixCoefficients (K : Type*) [CommSemiring K] (a b c : ℕ) :
    matMul K a b c = matrixCoefficients (K := K) (Fin a) (Fin b) (Fin c) := rfl

theorem matrixMultiplication_eq_matMul (a b c : ℕ) :
    matrixMultiplication a b c = matMul ℂ a b c := rfl

end MatrixMultiplication.Foundation.Tensor

end MatrixMultiplicationAllFields
