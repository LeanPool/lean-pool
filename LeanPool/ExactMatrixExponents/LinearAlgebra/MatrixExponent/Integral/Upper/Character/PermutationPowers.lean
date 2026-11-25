/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Permutations
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.DotsPower
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorCharacterPermutationPowers

/-!
# The exponents of the six permuted characters

The exponent identities below follow from evaluating the actual pairings at
dimension two. In particular, they do not depend on how the power-law witnesses
were chosen. Polynomial multiplication with one scalar input is identified
with the corresponding actual pairing by explicit coordinate equivalences.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass

/-- A scalar first input makes polynomial multiplication a single dot tensor. -/
theorem polynomialTensor_one_left_class (n : ℕ) :
    ofTensor (polynomialTensor 1 n) = dotX n :=
  TensorSpectrum.TensorClass.polynomialTensor_one_left_class n

namespace Character

theorem permuted_dotXValue (f : Character) (i : Fin 6) (n : ℕ) :
    (f.permuted i).dotXValue n =
      ![f.dotXValue n, f.dotYValue n, f.dotXValue n,
        f.dotYValue n, f.dotZValue n, f.dotZValue n] i :=
  TensorSpectrum.TensorClass.Character.permuted_dotXValue f i n

theorem permuted_pX (f : Character) (i : Fin 6) :
    (f.permuted i).pX = ![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i :=
  TensorSpectrum.TensorClass.Character.permuted_pX f i

theorem sum_permuted_pX (f : Character) :
    (∑ i : Fin 6, (f.permuted i).pX) = 2 * (f.pX + f.pY + f.pZ) :=
  TensorSpectrum.TensorClass.Character.sum_permuted_pX f

/-- The specialization of `meanExponent` to this coefficient ring. -/
abbrev meanExponent (f : Character) : ℝ :=
  TensorSpectrum.TensorClass.Character.meanExponent f

theorem meanExponent_nonneg (f : Character) : 0 ≤ f.meanExponent :=
  TensorSpectrum.TensorClass.Character.meanExponent_nonneg f

theorem meanExponent_le_one (f : Character) : f.meanExponent ≤ 1 :=
  TensorSpectrum.TensorClass.Character.meanExponent_le_one f

theorem sum_exponents_eq_three_meanExponent (f : Character) :
    f.pX + f.pY + f.pZ = 3 * f.meanExponent :=
  TensorSpectrum.TensorClass.Character.sum_exponents_eq_three_meanExponent f

theorem sum_permuted_pX_eq_six_meanExponent (f : Character) :
    (∑ i : Fin 6, (f.permuted i).pX) = 6 * f.meanExponent :=
  TensorSpectrum.TensorClass.Character.sum_permuted_pX_eq_six_meanExponent f

theorem sum_exponents_permuted (f : Character) (i : Fin 6) :
    (f.permuted i).pX + (f.permuted i).pY + (f.permuted i).pZ =
      f.pX + f.pY + f.pZ :=
  TensorSpectrum.TensorClass.Character.sum_exponents_permuted f i

theorem meanExponent_permuted (f : Character) (i : Fin 6) :
    (f.permuted i).meanExponent = f.meanExponent :=
  TensorSpectrum.TensorClass.Character.meanExponent_permuted f i

theorem permuted_polynomialTensor_one_left_value (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ) =
      (n : ℝ) ^ (f.permuted i).pX :=
  TensorSpectrum.TensorClass.Character.permuted_polynomialTensor_one_left_value f i n hn

theorem permuted_polynomialTensor_one_left_vector (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor 1 n)) : ℝ) =
      (n : ℝ) ^ (![f.pX, f.pY, f.pX, f.pY, f.pZ, f.pZ] i) :=
  TensorSpectrum.TensorClass.Character.permuted_polynomialTensor_one_left_vector f i n hn

theorem permuted_polynomialTensor_one_right_value (f : Character) (i : Fin 6) (n : ℕ) (hn : 1 ≤ n) :
    (f.permuted i (ofTensor (polynomialTensor n 1)) : ℝ) =
      (n : ℝ) ^ (f.permuted (permuteSwapXY i)).pX :=
  TensorSpectrum.TensorClass.Character.permuted_polynomialTensor_one_right_value f i n hn

end Character
end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper.TensorClass
