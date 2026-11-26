/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Semiring
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Rank
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassRankOrder

/-!
# Rank bounds and the concrete tensor order

Natural numbers in the quotient semiring are precisely the diagonal tensors.
These lemmas connect ordinary finite decompositions to the order used by states.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent.Upper.CoefficientTensor

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (ofTensor_zero natCast_eq_ofTensor_natTensor rank_add_le rank_mul_le le_rank_natCast
    rank_eq_zero_iff mul_le_rank_mul)

theorem one_le_of_ne_zero {A : TensorClass} (hA : A ≠ 0) : 1 ≤ A := by
  induction A using Quotient.inductionOn with | h a =>
    change ofRep a ≠ 0 at hA
    change 1 ≤ ofRep a
    have ha : a.coeff ≠ 0 := by
      intro h
      apply hA
      rw [← ofTensor_coeff a, h, ofTensor_zero]
    rw [← ofTensor_coeff a]
    have h := ofTensor_le (nonzero_restricts_natTensor_one ha)
    rw [MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.ofTensor_natTensor_one] at h
    exact h


namespace Character

theorem map_natCast (f : Character) (n : ℕ) : f n = n :=
  TensorSpectrum.TensorClass.Character.map_natCast f n

theorem le_rank (f : Character) (A : TensorClass) : f A ≤ rank A :=
  TensorSpectrum.TensorClass.Character.le_rank f A

end Character

theorem Character.one_le (f : Character) {A : TensorClass} (hA : A ≠ 0) : 1 ≤ f A := by
  have h := f.monotone' (one_le_of_ne_zero hA)
  simpa only [Character.map_one] using h

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
