/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite coefficient tensors and their algebraic transformations. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



open scoped BigOperators

namespace MatrixMultiplication.Foundation
namespace Tensor

section Pairing

variable {K U : Type*} [CommSemiring K] [DecidableEq U]

/-- The diagonal dot-pairing tensor, with a singleton third coordinate. -/
def dotPairing (U : Type*) [DecidableEq U] : Tensor K U U Unit :=
  fun i j _ => if i = j then 1 else 0

@[simp] theorem dotPairing_matching (i : U) :
    dotPairing (K := K) U i i () = 1 := by
  simp [dotPairing]

theorem contract_dotPairing [Fintype U] (a b : U → K) :
    contract (dotPairing (K := K) U) a b () = ∑ i, a i * b i := by
  classical
  simp [contract, dotPairing, ite_mul]

end Pairing

end Tensor
end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
