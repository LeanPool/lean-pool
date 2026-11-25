/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Semiring
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Rank
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
public import Mathlib.Logic.Equiv.Fin.Basic
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassDots

/-!
# Square matrix tensors in the restriction semiring

Dimension comparisons and multiplication are witnessed by the actual coordinate
maps. The cubic rank bound uses the ordinary sum over the three matrix indices.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
namespace CoefficientTensor

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor
  (matrixCoefficients_pullback_injective)

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor (squareProductCoordinates)

/-- Relabeling the product coordinates gives the larger square multiplication tensor. -/
theorem square_product_pullback (n m : ℕ) :
    Tensor.pullback (squareProductCoordinates n m) (squareProductCoordinates n m)
      (squareProductCoordinates n m) (Upper.matrixTensor (n * m) (n * m) (n * m)) =
      Tensor.product (Upper.matrixTensor n n n) (Upper.matrixTensor m m m) :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.square_product_pullback
    (K := O) n m

/-- Restrict a square multiplication tensor by taking the first indices of each wire. -/
theorem square_restricts_of_le {n m : ℕ} (h : n ≤ m) :
    Restricts (Upper.matrixTensor m m m) (Upper.matrixTensor n n n) :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.square_restricts_of_le
    (K := O) h

/-- A sum over the triples of indices gives a cubic rank bound. -/
theorem square_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Upper.matrixTensor n n n) (n ^ 3) :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.square_rankAtMost_cubic
    (K := O) n

end CoefficientTensor

namespace TensorClass

/-- The class of the actual `n` by `n` matrix multiplication tensor. -/
abbrev square := MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.square (K := O)

theorem square_mul (n m : ℕ) : square n * square m = square (n * m) := by
  unfold square TensorSpectrum.TensorClass.square
  rw [ofTensor_mul, ← TensorSpectrum.CoefficientTensor.square_product_pullback]
  exact ofTensor_pullback_equiv _ _ _ _

theorem square_mono {n m : ℕ} (h : n ≤ m) : square n ≤ square m :=
  ofTensor_le (CoefficientTensor.square_restricts_of_le h)

@[simp] theorem square_one : square 1 = 1 := by
  let e : (Fin 1 × Fin 1) ≃ PUnit :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => (0, 0)
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  have heq : Tensor.pullback e e e unitTensor = Upper.matrixTensor 1 1 1 := by
    funext x y z
    have h₁ : x.2 = y.1 := Subsingleton.elim _ _
    have h₂ : y.2 = z.1 := Subsingleton.elim _ _
    have h₃ : z.2 = x.1 := Subsingleton.elim _ _
    simp [Tensor.pullback, TensorSpectrum.TensorClass.unitTensor, Upper.matrixTensor,
      Tensor.matrixCoefficients, h₁, h₂, h₃]
  change ofTensor (Upper.matrixTensor 1 1 1) = ofTensor unitTensor
  rw [← heq]
  exact ofTensor_pullback_equiv _ e e e

theorem square_pow (n j : ℕ) : square (n ^ j) = square n ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, ← square_mul, ih, pow_succ]

/-- The rank here is the least size of an actual rank-one decomposition. -/
theorem rank_square_le (n : ℕ) : rank (square n) ≤ n ^ 3 := by
  rw [square, TensorSpectrum.TensorClass.square, rank_ofTensor]
  exact (CoefficientTensor.rank_le_iff _ _).mpr
    (CoefficientTensor.square_rankAtMost_cubic n)

theorem square_rank_upper (n : ℕ) : rank (square n) ≤ n ^ 3 := rank_square_le n

end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
