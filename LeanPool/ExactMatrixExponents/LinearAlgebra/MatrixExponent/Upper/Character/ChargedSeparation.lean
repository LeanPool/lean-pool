/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Character.Degeneration
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Upper.Separation
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialCharacterBounds

/-!
# The charged separation inequality for actual characters

The output is evaluated using full direct-sum additivity.  Exactly `5*M`
source copies are paid for, and the auxiliary dot product is retained.  In
the equal-value case the number of output blocks cancels the factor `M` in
that source cost, but never the auxiliary dot-product factor.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped BigOperators NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass

theorem Character.charged_separation (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (hM : 0 < M) (A : Fin M → Tensor Coeff X Y Z) :
    (∑ h, f (ofTensor (A h))) *
        f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      (5 * M : ℝ≥0) * f (ofTensor (Separation.shared A)) := by
  obtain ⟨P, hconstant, hdegree, heval⟩ := Separation.finite_charged_separation hM A
  have h := f.polynomial_constant_le
    (Tensor.directSum (fun _ : Fin (5 * M) => Separation.shared A))
    (Separation.separated A) P ((M - 1) ^ 2) hconstant hdegree heval
  exact TensorSpectrum.TensorClass.Character.charged_separation f 5 A h

/-- The block count pays the growing part of the separation cost.  The
remaining factor five is fixed, and is removed only in a later power limit. -/
theorem Character.charged_separation_equal (f : Character)
    {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    {M : ℕ} (hM : 0 < M) (A : Fin M → Tensor Coeff X Y Z)
    (c : ℝ≥0) (hvalue : ∀ h, f (ofTensor (A h)) = c) :
    c * f (ofTensor (Separation.dotPairingX (Fin M))) ≤
      5 * f (ofTensor (Separation.shared A)) :=
  TensorSpectrum.TensorClass.Character.charged_separation_equal f 5 hM A c hvalue
    (f.charged_separation hM A)

end MatrixMultiplicationAllFields.MatrixExponent.Upper.TensorClass
