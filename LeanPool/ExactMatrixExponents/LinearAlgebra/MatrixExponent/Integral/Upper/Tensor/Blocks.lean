/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Base
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.Blocks

/-!
# Heterogeneous direct sums and restrictions

The two summands retain separate coordinates on every leg. Cross coefficients
are zero, and block diagonal local matrices give actual restriction witnesses.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.CoefficientTensor

export MatrixMultiplicationAllFields.MatrixMultiplication.Foundation.Tensor
  (blockSum blockMatrix blockSum_inl blockSum_inr restrict_blockSum pullback_blockSum)

section Restriction

variable {X Y Z U V W X' Y' Z' U' V' W' : Type*}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

/-- Restriction is compatible with heterogeneous tensor direct sums. -/
theorem Restricts.blockSum
    {T : Tensor O X Y Z} {T' : Tensor O X' Y' Z'}
    {S : Tensor O U V W} {S' : Tensor O U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (blockSum T S) (blockSum T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨blockMatrix A D, blockMatrix B E, blockMatrix C F,
    (restrict_blockSum A B C D E F T S).symm⟩

/-- Restriction is compatible with tensor products through the actual products
of the three local coefficient matrices. -/
theorem Restricts.product
    {T : Tensor O X Y Z} {T' : Tensor O X' Y' Z'}
    {S : Tensor O U V W} {S' : Tensor O U' V' W'}
    (hT : Restricts T T') (hS : Restricts S S') :
    Restricts (Tensor.product T S) (Tensor.product T' S') := by
  rcases hT with ⟨A, B, C, rfl⟩
  rcases hS with ⟨D, E, F, rfl⟩
  exact ⟨fun x u => A x.1 u.1 * D x.2 u.2,
    fun y v => B y.1 v.1 * E y.2 v.2,
    fun z w => C z.1 w.1 * F z.2 w.2,
    (Tensor.restrict_product A B C D E F T S).symm⟩

end Restriction

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.CoefficientTensor
