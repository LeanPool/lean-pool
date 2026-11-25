/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Matrix
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.RankOrder
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassDots

/-!
# The three auxiliary pairings as actual tensor classes

The singleton leg is named in each pairing. Dimension comparisons select
coordinates, multiplication pairs coordinates, and the product of the three
orientations is the square matrix multiplication tensor.
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
  (dotUnitProduct dotTripleX dotTripleY dotTripleZ)

/-- The specialization of `dotXCoeff` to these coefficients. -/
abbrev dotXCoeff :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.dotXCoeff (K := O)

end CoefficientTensor

namespace TensorClass

/-- The specialization of `dotX` to these coefficients. -/
abbrev dotX :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.dotX (K := O)

/-- The specialization of `dotY` to these coefficients. -/
abbrev dotY :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.dotY (K := O)

/-- The specialization of `dotZ` to these coefficients. -/
abbrev dotZ :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.dotZ (K := O)

theorem dotX_mul (m n : ℕ) : dotX m * dotX n = dotX (m * n) :=
  TensorSpectrum.TensorClass.dotX_mul m n

theorem dotY_mul (m n : ℕ) : dotY m * dotY n = dotY (m * n) :=
  TensorSpectrum.TensorClass.dotY_mul m n

theorem dotZ_mul (m n : ℕ) : dotZ m * dotZ n = dotZ (m * n) :=
  TensorSpectrum.TensorClass.dotZ_mul m n

theorem one_le_dotX {n : ℕ} (hn : 0 < n) : 1 ≤ dotX n :=
  TensorSpectrum.TensorClass.one_le_dotX (n := n) hn

theorem one_le_dotY {n : ℕ} (hn : 0 < n) : 1 ≤ dotY n :=
  TensorSpectrum.TensorClass.one_le_dotY (n := n) hn

theorem one_le_dotZ {n : ℕ} (hn : 0 < n) : 1 ≤ dotZ n :=
  TensorSpectrum.TensorClass.one_le_dotZ (n := n) hn

namespace Character

/-- The specialization of `dotXValue` to this coefficient ring. -/
abbrev dotXValue (f : Character) (n : ℕ) : ℝ :=
  TensorSpectrum.TensorClass.Character.dotXValue f n

/-- The specialization of `dotYValue` to this coefficient ring. -/
abbrev dotYValue (f : Character) (n : ℕ) : ℝ :=
  TensorSpectrum.TensorClass.Character.dotYValue f n

/-- The specialization of `dotZValue` to this coefficient ring. -/
abbrev dotZValue (f : Character) (n : ℕ) : ℝ :=
  TensorSpectrum.TensorClass.Character.dotZValue f n

end Character
end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
