/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialSectors
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialTensor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialDegeneration
public import Lean.Elab.Tactic.Omega

/-!
# The three-sector polynomial degeneration

The coefficient identities describe three sectors. The first input has
weight zero throughout the degeneration.  Only when identifying the individual
middle branch do we reverse its first index; its other two indices are swapped.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper

export MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors
  (triplingWidth triplingYWeight triplingZWeight triplingMatched tripling_support_left
    tripling_support_right tripling_support_middle tripling_weight_nonneg
    tripling_weight_zero_iff tripling_weight_one_iff triplingGraded_of_weights
    triplingGraded_coefficient triplingLeftY triplingLeftZ triplingMiddleY triplingMiddleZ
    triplingRightY triplingRightZ triplingReverse triplingReverse_involutive
    tripling_left_weights tripling_middle_weights tripling_right_weights
    tripling_left_coefficient tripling_right_coefficient tripling_middle_coefficient
    tripling_second_sectors_disjoint tripling_output_sectors_disjoint TriplingY TriplingZ
    triplingYMap triplingZMap triplingYMap_injective triplingZMap_injective
    triplingYMap_surjective triplingZMap_surjective triplingYEquiv triplingZEquiv
    triplingGraded_sector_assembly)

/-- The shared triplingGraded construction over the coefficient ring. -/
abbrev triplingGraded :=
  MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors.triplingGraded (K := Coeff)

/-- The shared triplingSectorTensor construction over the coefficient ring. -/
abbrev triplingSectorTensor :=
  MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors.triplingSectorTensor (K := Coeff)

end MatrixMultiplicationAllFields.MatrixExponent.Upper
