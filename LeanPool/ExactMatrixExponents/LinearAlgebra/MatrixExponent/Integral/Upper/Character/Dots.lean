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

/-- The specialization of `dotYCoeff` to these coefficients. -/
abbrev dotYCoeff :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.dotYCoeff (K := O)

/-- The specialization of `dotZCoeff` to these coefficients. -/
abbrev dotZCoeff :=
  MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.dotZCoeff (K := O)

theorem dotX_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotXCoeff n) (dotXCoeff m) :=
  TensorSpectrum.CoefficientTensor.dotX_restricts_of_le (m := m) (n := n) h

theorem dotY_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotYCoeff n) (dotYCoeff m) :=
  TensorSpectrum.CoefficientTensor.dotY_restricts_of_le (m := m) (n := n) h

theorem dotZ_restricts_of_le {m n : ℕ} (h : m ≤ n) :
    Restricts (dotZCoeff n) (dotZCoeff m) :=
  TensorSpectrum.CoefficientTensor.dotZ_restricts_of_le (m := m) (n := n) h

theorem dotX_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotXCoeff n) n :=
  TensorSpectrum.CoefficientTensor.dotX_rankAtMost n

theorem dotY_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotYCoeff n) n :=
  TensorSpectrum.CoefficientTensor.dotY_rankAtMost n

theorem dotZ_rankAtMost (n : ℕ) : Tensor.RankAtMost (dotZCoeff n) n :=
  TensorSpectrum.CoefficientTensor.dotZ_rankAtMost n

theorem dotX_product_pullback (m n : ℕ) :
    Tensor.pullback dotUnitProduct
      (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)) finProdFinEquiv
      (dotXCoeff (m * n)) = Tensor.product (dotXCoeff m) (dotXCoeff n) :=
  TensorSpectrum.CoefficientTensor.dotX_product_pullback m n

theorem dotY_product_pullback (m n : ℕ) :
    Tensor.pullback (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
      dotUnitProduct finProdFinEquiv (dotYCoeff (m * n)) =
      Tensor.product (dotYCoeff m) (dotYCoeff n) :=
  TensorSpectrum.CoefficientTensor.dotY_product_pullback m n

theorem dotZ_product_pullback (m n : ℕ) :
    Tensor.pullback (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))
      finProdFinEquiv dotUnitProduct (dotZCoeff (m * n)) =
      Tensor.product (dotZCoeff m) (dotZCoeff n) :=
  TensorSpectrum.CoefficientTensor.dotZ_product_pullback m n

theorem dotTriple_pullback (n : ℕ) :
    Tensor.pullback (dotTripleX n) (dotTripleY n) (dotTripleZ n)
      (Upper.matrixTensor n n n) =
      Tensor.product (Tensor.product (dotXCoeff n) (dotYCoeff n)) (dotZCoeff n) :=
  TensorSpectrum.CoefficientTensor.dotTriple_pullback n

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

theorem dotX_mono {m n : ℕ} (h : m ≤ n) : dotX m ≤ dotX n :=
  TensorSpectrum.TensorClass.dotX_mono (m := m) (n := n) h

theorem dotY_mono {m n : ℕ} (h : m ≤ n) : dotY m ≤ dotY n :=
  TensorSpectrum.TensorClass.dotY_mono (m := m) (n := n) h

theorem dotZ_mono {m n : ℕ} (h : m ≤ n) : dotZ m ≤ dotZ n :=
  TensorSpectrum.TensorClass.dotZ_mono (m := m) (n := n) h

theorem rank_dotX_le (n : ℕ) : rank (dotX n) ≤ n :=
  TensorSpectrum.TensorClass.rank_dotX_le n

theorem rank_dotY_le (n : ℕ) : rank (dotY n) ≤ n :=
  TensorSpectrum.TensorClass.rank_dotY_le n

theorem rank_dotZ_le (n : ℕ) : rank (dotZ n) ≤ n :=
  TensorSpectrum.TensorClass.rank_dotZ_le n

theorem dotX_mul (m n : ℕ) : dotX m * dotX n = dotX (m * n) :=
  TensorSpectrum.TensorClass.dotX_mul m n

theorem dotY_mul (m n : ℕ) : dotY m * dotY n = dotY (m * n) :=
  TensorSpectrum.TensorClass.dotY_mul m n

theorem dotZ_mul (m n : ℕ) : dotZ m * dotZ n = dotZ (m * n) :=
  TensorSpectrum.TensorClass.dotZ_mul m n

theorem dotX_one : dotX 1 = 1 :=
  TensorSpectrum.TensorClass.dotX_one

theorem dotY_one : dotY 1 = 1 :=
  TensorSpectrum.TensorClass.dotY_one

theorem dotZ_one : dotZ 1 = 1 :=
  TensorSpectrum.TensorClass.dotZ_one

theorem one_le_dotX {n : ℕ} (hn : 0 < n) : 1 ≤ dotX n :=
  TensorSpectrum.TensorClass.one_le_dotX (n := n) hn

theorem one_le_dotY {n : ℕ} (hn : 0 < n) : 1 ≤ dotY n :=
  TensorSpectrum.TensorClass.one_le_dotY (n := n) hn

theorem one_le_dotZ {n : ℕ} (hn : 0 < n) : 1 ≤ dotZ n :=
  TensorSpectrum.TensorClass.one_le_dotZ (n := n) hn

theorem dotX_mul_dotY_mul_dotZ (n : ℕ) : dotX n * dotY n * dotZ n = square n :=
  TensorSpectrum.TensorClass.dotX_mul_dotY_mul_dotZ n


namespace Character

theorem dotX_le (f : Character) (n : ℕ) : f (dotX n) ≤ n :=
  TensorSpectrum.TensorClass.Character.dotX_le f n

theorem dotY_le (f : Character) (n : ℕ) : f (dotY n) ≤ n :=
  TensorSpectrum.TensorClass.Character.dotY_le f n

theorem dotZ_le (f : Character) (n : ℕ) : f (dotZ n) ≤ n :=
  TensorSpectrum.TensorClass.Character.dotZ_le f n

theorem one_le_dotX (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotX n) :=
  TensorSpectrum.TensorClass.Character.one_le_dotX f hn

theorem one_le_dotY (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotY n) :=
  TensorSpectrum.TensorClass.Character.one_le_dotY f hn

theorem one_le_dotZ (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f (dotZ n) :=
  TensorSpectrum.TensorClass.Character.one_le_dotZ f hn

/-- The specialization of `dotXValue` to this coefficient ring. -/
abbrev dotXValue (f : Character) (n : ℕ) : ℝ :=
  TensorSpectrum.TensorClass.Character.dotXValue f n

/-- The specialization of `dotYValue` to this coefficient ring. -/
abbrev dotYValue (f : Character) (n : ℕ) : ℝ :=
  TensorSpectrum.TensorClass.Character.dotYValue f n

/-- The specialization of `dotZValue` to this coefficient ring. -/
abbrev dotZValue (f : Character) (n : ℕ) : ℝ :=
  TensorSpectrum.TensorClass.Character.dotZValue f n

theorem dotXValue_nonneg (f : Character) (n : ℕ) : 0 ≤ f.dotXValue n :=
  TensorSpectrum.TensorClass.Character.dotXValue_nonneg f n

theorem dotYValue_nonneg (f : Character) (n : ℕ) : 0 ≤ f.dotYValue n :=
  TensorSpectrum.TensorClass.Character.dotYValue_nonneg f n

theorem dotZValue_nonneg (f : Character) (n : ℕ) : 0 ≤ f.dotZValue n :=
  TensorSpectrum.TensorClass.Character.dotZValue_nonneg f n

theorem dotXValue_le (f : Character) (n : ℕ) : f.dotXValue n ≤ n :=
  TensorSpectrum.TensorClass.Character.dotXValue_le f n

theorem dotYValue_le (f : Character) (n : ℕ) : f.dotYValue n ≤ n :=
  TensorSpectrum.TensorClass.Character.dotYValue_le f n

theorem dotZValue_le (f : Character) (n : ℕ) : f.dotZValue n ≤ n :=
  TensorSpectrum.TensorClass.Character.dotZValue_le f n

theorem one_le_dotXValue (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotXValue n :=
  TensorSpectrum.TensorClass.Character.one_le_dotXValue f hn

theorem one_le_dotYValue (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotYValue n :=
  TensorSpectrum.TensorClass.Character.one_le_dotYValue f hn

theorem one_le_dotZValue (f : Character) {n : ℕ} (hn : 0 < n) : 1 ≤ f.dotZValue n :=
  TensorSpectrum.TensorClass.Character.one_le_dotZValue f hn

theorem dotXValue_mono (f : Character) : Monotone f.dotXValue :=
  TensorSpectrum.TensorClass.Character.dotXValue_mono f

theorem dotYValue_mono (f : Character) : Monotone f.dotYValue :=
  TensorSpectrum.TensorClass.Character.dotYValue_mono f

theorem dotZValue_mono (f : Character) : Monotone f.dotZValue :=
  TensorSpectrum.TensorClass.Character.dotZValue_mono f

theorem dotXValue_mul (f : Character) (m n : ℕ) :
    f.dotXValue (m * n) = f.dotXValue m * f.dotXValue n :=
  TensorSpectrum.TensorClass.Character.dotXValue_mul f m n

theorem dotYValue_mul (f : Character) (m n : ℕ) :
    f.dotYValue (m * n) = f.dotYValue m * f.dotYValue n :=
  TensorSpectrum.TensorClass.Character.dotYValue_mul f m n

theorem dotZValue_mul (f : Character) (m n : ℕ) :
    f.dotZValue (m * n) = f.dotZValue m * f.dotZValue n :=
  TensorSpectrum.TensorClass.Character.dotZValue_mul f m n

theorem dotXValue_one (f : Character) : f.dotXValue 1 = 1 :=
  TensorSpectrum.TensorClass.Character.dotXValue_one f

theorem dotYValue_one (f : Character) : f.dotYValue 1 = 1 :=
  TensorSpectrum.TensorClass.Character.dotYValue_one f

theorem dotZValue_one (f : Character) : f.dotZValue 1 = 1 :=
  TensorSpectrum.TensorClass.Character.dotZValue_one f

theorem dotValues_product (f : Character) (n : ℕ) :
    f.dotXValue n * f.dotYValue n * f.dotZValue n = f (square n) :=
  TensorSpectrum.TensorClass.Character.dotValues_product f n

end Character
end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
