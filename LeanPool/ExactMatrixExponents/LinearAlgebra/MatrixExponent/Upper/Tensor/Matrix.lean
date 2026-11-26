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
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Flattening
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
public import Mathlib.Logic.Equiv.Fin.Basic
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassDots

/-!
# Square matrix tensors in the restriction semiring

Dimension comparisons and multiplication are witnessed by the actual coordinate
maps. The cubic rank bound uses the ordinary sum over the three matrix indices.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper
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
    (K := Coeff) n m

/-- Restrict a square multiplication tensor by taking the first indices of each wire. -/
theorem square_restricts_of_le {n m : ℕ} (h : n ≤ m) :
    Restricts (Upper.matrixTensor m m m) (Upper.matrixTensor n n n) :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.square_restricts_of_le
    (K := Coeff) h

/-- A sum over the triples of indices gives a cubic rank bound. -/
theorem square_rankAtMost_cubic (n : ℕ) :
    Tensor.RankAtMost (Upper.matrixTensor n n n) (n ^ 3) :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.square_rankAtMost_cubic
    (K := Coeff) n

end CoefficientTensor

namespace TensorClass

/-- The class of the actual `n` by `n` matrix multiplication tensor. -/
abbrev square := MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.square (K := Coeff)

theorem rank_square_le (n : ℕ) : rank (square n) ≤ n ^ 3 :=
  TensorSpectrum.TensorClass.rank_square_le n

theorem flatteningRank_square (n : ℕ) : flatteningRank (square n) = n ^ 2 := by
  rw [square, TensorSpectrum.TensorClass.square, flatteningRank_ofTensor]
  exact CoefficientTensor.flatteningRank_square n

theorem square_rank_lower (n : ℕ) : n ^ 2 ≤ rank (square n) := by
  rw [← flatteningRank_square n]
  exact flatteningRank_le_rank (square n)

end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Upper
