/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Tensor.Semiring
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialTensor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.Dots
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Tactic.FinCases
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassPermutations

/-!
# Permuting the three actual tensor legs

The two adjacent swaps act on coefficient arrays and on their actual local
restriction witnesses. Their quotient actions preserve the semiring operations.
The six induced characters therefore remain normalized restriction-monotone
characters; their six values form a multiset invariant under either swap.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper
namespace CoefficientTensor

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor
  (swapXY swapYZ swapXY_blockSum swapYZ_blockSum swapXY_product swapYZ_product)

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.CoefficientTensor.Restricts
  (swapXY swapYZ)

end Restricts
end CoefficientTensor

namespace TensorRep

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep
  (swapXY swapYZ)

namespace Restricts

export MatrixMultiplicationAllFields.TensorSpectrum.TensorRep.Restricts
  (swapXY swapYZ)

end Restricts
end TensorRep

namespace TensorClass

/-- The specialization of `swapXY` to these coefficients. -/
abbrev swapXY :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.swapXY (K := Coeff)

/-- The specialization of `swapYZ` to these coefficients. -/
abbrev swapYZ :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.swapYZ (K := Coeff)

theorem swapXY_mono : Monotone swapXY :=
  TensorSpectrum.TensorClass.swapXY_mono

theorem swapYZ_mono : Monotone swapYZ :=
  TensorSpectrum.TensorClass.swapYZ_mono

theorem swapXY_zero : swapXY (0 : TensorClass) = 0 :=
  TensorSpectrum.TensorClass.swapXY_zero

theorem swapYZ_zero : swapYZ (0 : TensorClass) = 0 :=
  TensorSpectrum.TensorClass.swapYZ_zero

theorem swapXY_one : swapXY (1 : TensorClass) = 1 :=
  TensorSpectrum.TensorClass.swapXY_one

theorem swapYZ_one : swapYZ (1 : TensorClass) = 1 :=
  TensorSpectrum.TensorClass.swapYZ_one

/-- The specialization of `swapXYHom` to these coefficients. -/
abbrev swapXYHom :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.swapXYHom (K := Coeff)

/-- The specialization of `swapYZHom` to these coefficients. -/
abbrev swapYZHom :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.swapYZHom (K := Coeff)

/-- The specialization of `permuteHom` to these coefficients. -/
abbrev permuteHom :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.permuteHom (K := Coeff)

/-- The specialization of `permute` to these coefficients. -/
abbrev permute :=
  MatrixMultiplicationAllFields.TensorSpectrum.TensorClass.permute (K := Coeff)

theorem permute_mono (i : Fin 6) : Monotone (permute i) :=
  TensorSpectrum.TensorClass.permute_mono i

theorem swapXY_polynomialTensor (a b : ℕ) :
    swapXY (ofTensor (polynomialTensor a b)) = ofTensor (polynomialTensor b a) :=
  TensorSpectrum.TensorClass.swapXY_polynomialTensor a b

theorem swapXY_dotX (n : ℕ) : swapXY (dotX n) = dotY n :=
  TensorSpectrum.TensorClass.swapXY_dotX n

theorem swapXY_dotY (n : ℕ) : swapXY (dotY n) = dotX n :=
  TensorSpectrum.TensorClass.swapXY_dotY n

theorem swapXY_dotZ (n : ℕ) : swapXY (dotZ n) = dotZ n :=
  TensorSpectrum.TensorClass.swapXY_dotZ n

theorem swapYZ_dotX (n : ℕ) : swapYZ (dotX n) = dotX n :=
  TensorSpectrum.TensorClass.swapYZ_dotX n

theorem swapYZ_dotY (n : ℕ) : swapYZ (dotY n) = dotZ n :=
  TensorSpectrum.TensorClass.swapYZ_dotY n

theorem swapYZ_dotZ (n : ℕ) : swapYZ (dotZ n) = dotY n :=
  TensorSpectrum.TensorClass.swapYZ_dotZ n

theorem swapXY_square (n : ℕ) : swapXY (square n) = square n :=
  TensorSpectrum.TensorClass.swapXY_square n

theorem swapYZ_square (n : ℕ) : swapYZ (square n) = square n :=
  TensorSpectrum.TensorClass.swapYZ_square n

theorem permute_square (i : Fin 6) (n : ℕ) : permute i (square n) = square n :=
  TensorSpectrum.TensorClass.permute_square i n

export MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
  (swapXY_ofTensor swapYZ_ofTensor swapXY_swapXY swapYZ_swapYZ swap_braid swapXY_add swapYZ_add
    swapXY_mul swapYZ_mul permuteSwapXY permuteSwapYZ permute_swapXY permute_swapYZ)

namespace Character

/-- The specialization of `permuted` to this coefficient ring. -/
abbrev permuted (f : Character) (i : Fin 6) : Character :=
  TensorSpectrum.TensorClass.Character.permuted f i

theorem permuted_apply (f : Character) (i : Fin 6) (T : TensorClass) :
    f.permuted i T = f (permute i T) :=
  TensorSpectrum.TensorClass.Character.permuted_apply f i T

theorem permuted_swapXY (f : Character) (i : Fin 6) (T : TensorClass) :
    f.permuted i (swapXY T) = f.permuted (permuteSwapXY i) T :=
  TensorSpectrum.TensorClass.Character.permuted_swapXY f i T

theorem permuted_swapYZ (f : Character) (i : Fin 6) (T : TensorClass) :
    f.permuted i (swapYZ T) = f.permuted (permuteSwapYZ i) T :=
  TensorSpectrum.TensorClass.Character.permuted_swapYZ f i T

/-- The specialization of `sixValues` to this coefficient ring. -/
abbrev sixValues (f : Character) (T : TensorClass) : Multiset ℝ≥0 :=
  TensorSpectrum.TensorClass.Character.sixValues f T

theorem sixValues_swapXY (f : Character) (T : TensorClass) :
    f.sixValues (swapXY T) = f.sixValues T :=
  TensorSpectrum.TensorClass.Character.sixValues_swapXY f T

theorem sixValues_swapYZ (f : Character) (T : TensorClass) :
    f.sixValues (swapYZ T) = f.sixValues T :=
  TensorSpectrum.TensorClass.Character.sixValues_swapYZ f T

theorem sixValues_polynomialTensor_swap (f : Character) (a b : ℕ) :
    f.sixValues (ofTensor (polynomialTensor a b)) =
      f.sixValues (ofTensor (polynomialTensor b a)) :=
  TensorSpectrum.TensorClass.Character.sixValues_polynomialTensor_swap f a b

theorem permuted_square (f : Character) (i : Fin 6) (n : ℕ) :
    f.permuted i (square n) = f (square n) :=
  TensorSpectrum.TensorClass.Character.permuted_square f i n

theorem permuted_dotX (f : Character) (i : Fin 6) (n : ℕ) :
    f.permuted i (dotX n) = ![f (dotX n), f (dotY n), f (dotX n),
      f (dotY n), f (dotZ n), f (dotZ n)] i :=
  TensorSpectrum.TensorClass.Character.permuted_dotX f i n

theorem sixValues_dotX (f : Character) (n : ℕ) :
    f.sixValues (dotX n) =
      ({f (dotX n)} + {f (dotY n)} + {f (dotZ n)}) +
      ({f (dotX n)} + {f (dotY n)} + {f (dotZ n)}) :=
  TensorSpectrum.TensorClass.Character.sixValues_dotX f n

end Character
end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Upper
