/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialFiltration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialTensor
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.PolynomialDegeneration
public import Lean.Elab.Tactic.Omega

/-!
# The explicit determinant filtration

We use positive dimensions `a+1` and `b+2`.  The two old copies are the
coefficients of `s` and `w`.  The new coordinates are quotient lifts `Q` and
kernel elements `K = W_j - S_(j+1)`.  The first input is unchanged throughout.
All statements below are coefficient identities over the coefficient field.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent

noncomputable section
open scoped BigOperators
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper

export MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors
  (doubleIndexEquiv doubleOutputEquiv determinant_basis_change
    determinantGraded_quotient determinantGraded_kernel determinantGraded_quotient_kernel
    determinantGraded_kernel_quotient determinantInputWeight determinantOutputWeight
    determinant_supported_weight determinant_weightedLimit)

/-- The shared delta construction over the coefficient ring. -/
abbrev delta {ι : Type*} [DecidableEq ι] (i j : ι) :=
  TensorSpectrum.PolynomialTensors.delta (K := Coeff) i j

/-- The shared doubledPolynomialTensor construction over the coefficient ring. -/
abbrev doubledPolynomialTensor :=
  TensorSpectrum.PolynomialTensors.doubledPolynomialTensor (K := Coeff)

/-- The shared binaryDotTensor construction over the coefficient ring. -/
abbrev binaryDotTensor :=
  TensorSpectrum.PolynomialTensors.binaryDotTensor (K := Coeff)

/-- The shared determinantInputMap construction over the coefficient ring. -/
abbrev determinantInputMap :=
  TensorSpectrum.PolynomialTensors.determinantInputMap (K := Coeff)

/-- The shared determinantOutputMap construction over the coefficient ring. -/
abbrev determinantOutputMap :=
  TensorSpectrum.PolynomialTensors.determinantOutputMap (K := Coeff)

/-- The shared determinantAdaptedTensor construction over the coefficient ring. -/
abbrev determinantAdaptedTensor :=
  TensorSpectrum.PolynomialTensors.determinantAdaptedTensor (K := Coeff)

/-- The shared determinantGradedTensor construction over the coefficient ring. -/
abbrev determinantGradedTensor :=
  TensorSpectrum.PolynomialTensors.determinantGradedTensor (K := Coeff)

/-- Relabeling gives two copies of convolution with the first input shared. -/
theorem doubledPolynomialTensor_product (a b : ℕ) :
    Tensor.pullback (fun i => (i, ())) (doubleIndexEquiv (b + 2))
      (doubleOutputEquiv a b)
      (Tensor.product (polynomialTensor (a + 1) (b + 2)) binaryDotTensor) =
      doubledPolynomialTensor a b :=
  TensorSpectrum.PolynomialTensors.doubledPolynomialTensor_product (K := Coeff) a b

end MatrixMultiplicationAllFields.MatrixExponent.Upper
