/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Tag
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.PolynomialDegeneration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.PolynomialValues
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.TagHeterogeneous
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagPolynomialBranches
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Permutations
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Weighted
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialGrowth

/-!
# The weighted growth bound for actual tensor characters

Use the optimized tag inequality on the determinant and tripling
degenerations for each leg permutation separately.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Integral
open Rectangle
open Upper Upper.TensorClass Upper.TagHeterogeneous

/-- The character value of convolution with positive input lengths. -/
abbrev poly (f : Character) (m n : ℕ) : ℝ :=
  TensorSpectrum.PolynomialGrowth.poly f m n

theorem poly_row (f : Character) (hp : 0 < f.pX) (m : ℕ) :
    Row (fun n => poly f m n ^ (1 / f.pX))
      (fun n => (f (swapYZ (ofTensor (polynomialTensor (m + 1) (n + 1)))) : ℝ) ^ (1 / f.pX)) m :=
  TensorSpectrum.PolynomialGrowth.poly_row
    Character.polynomial_value_pos
    Character.shared_tag_optimized_of_pos
    Character.determinant_graded_le Character.tripling_graded_le f hp m

theorem character_bound (f : Character) (A B C : ℕ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) :
    4 * (f.pX * B * C + f.pY * A * C + f.pZ * A * B) ≤ ((A : ℝ) + B + C) ^ 2 :=
  TensorSpectrum.PolynomialGrowth.character_bound
    Character.polynomial_value_pos
    Character.shared_tag_optimized_of_pos
    Character.determinant_graded_le Character.tripling_graded_le
    Character.polynomial_value_le f A B C hA hB hC

end MatrixMultiplicationAllFields.MatrixExponent.Integral
