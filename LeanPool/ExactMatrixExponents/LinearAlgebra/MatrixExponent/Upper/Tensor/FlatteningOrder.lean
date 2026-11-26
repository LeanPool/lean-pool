/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.RankOrder
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Flattening

/-! The actual additive flattening invariant on the concrete tensor semiring. -/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

@[simp] theorem flatteningRank_natCast (n : ℕ) : flatteningRank (n : TensorClass) = n := by
  rw [natCast_eq_ofTensor_natTensor, flatteningRank_ofTensor,
    CoefficientTensor.flatteningRank_natTensor]

@[simp] theorem flatteningRank_zero : flatteningRank (0 : TensorClass) = 0 :=
  flatteningRank_natCast 0

@[simp] theorem flatteningRank_one : flatteningRank (1 : TensorClass) = 1 := by
  simpa only [Nat.cast_one] using flatteningRank_natCast 1

theorem flatteningRank_add (A B : TensorClass) :
    flatteningRank (A + B) = flatteningRank A + flatteningRank B := by
  induction A using Quotient.inductionOn with | h a =>
    induction B using Quotient.inductionOn with | h b =>
      change flatteningRank (ofRep a + ofRep b) =
        flatteningRank (ofRep a) + flatteningRank (ofRep b)
      rw [← ofTensor_coeff a, ← ofTensor_coeff b, ofTensor_add]
      simp only [flatteningRank_ofTensor, CoefficientTensor.flatteningRank_blockSum]

@[simp] theorem rank_natCast (n : ℕ) : rank (n : TensorClass) = n := by
  apply Nat.le_antisymm
  · rw [natCast_eq_ofTensor_natTensor, rank_ofTensor]
    exact (CoefficientTensor.rank_le_iff _ _).mpr
      (CoefficientTensor.rankAtMost_natTensor n)
  · simpa only [flatteningRank_natCast] using
      flatteningRank_le_rank (n : TensorClass)

theorem natCast_le_natCast_iff (m n : ℕ) :
    (m : TensorClass) ≤ (n : TensorClass) ↔ m ≤ n := by
  constructor
  · intro h
    simpa only [rank_natCast] using rank_mono h
  · intro h
    rw [natCast_eq_ofTensor_natTensor, natCast_eq_ofTensor_natTensor]
    exact ofTensor_le (CoefficientTensor.natTensor_restricts_of_le h)

/-- A positive scalar cannot be absorbed by a finite catalyst. This is where
additive flattening rank is used, rather than additivity of ordinary rank. -/
theorem not_add_positive_natCast_le (D : TensorClass) {m : ℕ} (hm : 0 < m) :
    ¬ D + (m : TensorClass) ≤ D := by
  intro h
  have hf := flatteningRank_mono h
  rw [flatteningRank_add, flatteningRank_natCast] at hf
  exact (Nat.not_lt_of_ge hf) (Nat.lt_add_of_pos_right hm)

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
