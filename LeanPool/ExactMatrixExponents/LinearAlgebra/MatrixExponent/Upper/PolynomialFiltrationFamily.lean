/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialFiltration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialWeightFamily
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialFiltrationFamily

/-!
# The finite-degree determinant family

The constant coefficient is the two-branch graded tensor.  Every nonzero
evaluation is an actual restriction of the original convolution tensor times
the two-dimensional pairing.  These explicit data, rather than continuity of
an arbitrary tensor character, are the inputs to finite interpolation.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper

theorem determinantAdapted_mem_restrictionOrbit (a b : ℕ) :
    determinantAdaptedTensor a b ∈ LocalTensor.orbit
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) :=
  TensorSpectrum.PolynomialTensors.determinantAdapted_mem_restrictionOrbit a b

/-- The determinant polynomial family over the coefficient ring. -/
abbrev determinantPolynomialFamily :=
  TensorSpectrum.PolynomialTensors.determinantPolynomialFamily (K := Coeff)

theorem determinantPolynomialFamily_coeff_zero (a b : ℕ) :
    (fun i y z => (determinantPolynomialFamily a b i y z).coeff 0) =
      determinantGradedTensor a b :=
  TensorSpectrum.PolynomialTensors.determinantPolynomialFamily_coeff_zero a b

theorem determinantPolynomialFamily_degree_le (a b : ℕ)
    (i : Fin (a + 1)) (y : Fin (b + 3) ⊕ Fin (b + 1))
    (z : Fin (a + b + 3) ⊕ Fin (a + b + 1)) :
    (determinantPolynomialFamily a b i y z).degree ≤ (1 : ℕ) :=
  TensorSpectrum.PolynomialTensors.determinantPolynomialFamily_degree_le a b i y z

theorem determinantPolynomialFamily_eval_mem_restrictionOrbit (a b : ℕ)
    {t : Coeff} (ht : t ≠ 0) :
    (fun i y z => (determinantPolynomialFamily a b i y z).eval t) ∈
      LocalTensor.orbit
        (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) := by
  have h := weightedPolynomial_eval_mem_restrictionOrbit
    (determinantAdaptedTensor a b) (fun _ => 0)
    (determinantInputWeight b) (determinantOutputWeight a b)
    (determinant_supported_weight a b) ht
  exact restrictionOrbit_trans (determinantAdapted_mem_restrictionOrbit a b) h

end MatrixMultiplicationAllFields.MatrixExponent.Upper
