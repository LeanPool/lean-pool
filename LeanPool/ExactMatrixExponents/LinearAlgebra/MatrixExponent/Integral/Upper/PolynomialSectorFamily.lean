/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialSectors
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialWeightFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialSectorFamily

/-!
# The polynomial witness for the three-sector degeneration

Every coefficient has degree at most one.  Its constant coefficient is the
entire shared-first-input sector assembly.  At each nonzero parameter the
evaluated tensor is an actual restriction of the original polynomial tensor.
These explicit facts support interpolation without assuming that an arbitrary
tensor character preserves topological limits.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper

/-- The tripling polynomial family over the coefficient ring. -/
abbrev triplingPolynomialFamily :=
  TensorSpectrum.PolynomialTensors.triplingPolynomialFamily (K := O)

theorem triplingPolynomialFamily_coeff_zero (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).coeff 0 = triplingSectorTensor a h x y z :=
  TensorSpectrum.PolynomialTensors.triplingPolynomialFamily_coeff_zero a h ha hh x y z

theorem triplingPolynomialFamily_degree_le (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h)
    (x : Fin a) (y : TriplingY a h) (z : TriplingZ a h) :
    (triplingPolynomialFamily a h ha hh x y z).degree ≤ (1 : ℕ) :=
  TensorSpectrum.PolynomialTensors.triplingPolynomialFamily_degree_le a h ha hh x y z

/-- Every nonzero evaluation is an exact restriction of the original source
tensor. The sector reindexing is one fixed pair of local maps, with identity
on the common first input, after the diagonal maps. -/
theorem triplingPolynomialFamily_eval_mem_restrictionOrbit
    (a h : ℕ) (ha : 1 ≤ a) (hh : 1 ≤ h) {t : O} (ht : IsUnit t) :
    (fun x y z => (triplingPolynomialFamily a h ha hh x y z).eval t) ∈
      LocalTensor.orbit (polynomialTensor a (triplingWidth a h)) :=
  TensorSpectrum.PolynomialTensors.triplingPolynomialFamily_eval_mem_restrictionOrbit a h ha hh t
    (weightedPolynomial_eval_mem_restrictionOrbit _ _ _ _
      (TensorSpectrum.PolynomialTensors.tripling_source_weights_nonneg a h ha) ht)

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
