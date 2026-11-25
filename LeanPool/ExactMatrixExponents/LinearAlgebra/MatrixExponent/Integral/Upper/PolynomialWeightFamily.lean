/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.PolynomialDegeneration
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.WeightedPolynomials

/-!
# Explicit polynomial families for diagonal weight degenerations

The diagonal degeneration has a polynomial coefficient family, not merely a
topological limit. Its constant coefficient is the retained tensor. Its degree
is controlled by the supported total weights. At every nonzero parameter its
evaluation is an exact restriction of the source tensor. These are the inputs
needed to extract tensor powers by finite interpolation.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

noncomputable section

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper

variable {X Y Z : Type*}

export MatrixMultiplicationAllFields.TensorSpectrum.PolynomialTensors
  (weightedPolynomial weightedPolynomial_eval weightedPolynomial_coeff_zero
    weightedPolynomial_natDegree_le weightedPolynomial_degree_le
    weightedPolynomial_degree_le_one)

/-- Every nonzero evaluation has actual diagonal local restriction witnesses;
the polynomial family does not assume a character or a continuity principle. -/
theorem weightedPolynomial_eval_mem_restrictionOrbit
    [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor O X Y Z) (wx : X → ℤ) (wy : Y → ℤ) (wz : Z → ℤ)
    (h : ∀ x y z, T x y z ≠ 0 → 0 ≤ wx x + wy y + wz z)
    {t : O} (ht : IsUnit t) :
    (fun x y z => (weightedPolynomial T wx wy wz x y z).eval t) ∈
      LocalTensor.orbit T := by
  rw [weightedPolynomial_eval]
  exact weightedFamily_mem_restrictionOrbit T wx wy wz h ht

/-- Actual local restriction witnesses compose without a limiting argument. -/
theorem restrictionOrbit_trans
    {X' Y' Z' X'' Y'' Z'' : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    {T : Tensor O X Y Z} {U : Tensor O X' Y' Z'} {V : Tensor O X'' Y'' Z''}
    (hTU : U ∈ LocalTensor.orbit T)
    (hUV : V ∈ LocalTensor.orbit U) :
    V ∈ LocalTensor.orbit T := by
  obtain ⟨a, b, c, rfl⟩ := hUV
  exact LocalTensor.restrict_mem hTU a b c

end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
