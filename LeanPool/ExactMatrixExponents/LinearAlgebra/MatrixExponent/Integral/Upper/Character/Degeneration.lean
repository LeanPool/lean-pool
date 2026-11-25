/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagGrowth
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Coefficients
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.Tensor.Powers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Integral.Upper.SeparationInterpolation
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.CharacterDegeneration

/-!
# Characters and polynomial degenerations

Restriction monotonicity suffices for a polynomial degeneration.  For each
fixed family, interpolation of its tensor powers costs only linearly many
copies.  The elementary estimate below removes that overhead without any
assumed continuity of the character.
-/

@[expose] public section

open MatrixMultiplicationAllFields.MatrixExponent.Integral
    MatrixMultiplicationAllFields.TensorSpectrum

noncomputable section

open scoped NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

namespace MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper

export MatrixMultiplicationAllFields.TensorSpectrum (le_of_pow_le_linear_mul_pow)

namespace TensorClass

/-- Every normalized restriction-monotone character is monotone on the
constant coefficient of an actual bounded polynomial restriction family.
The degree is fixed before the tensor-power argument is applied. -/
theorem Character.polynomial_constant_le (f : Character)
    {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor O X Y Z) (D : Tensor O U V W)
    (P : Tensor (Polynomial O) U V W) (K : ℕ)
    (hconstant : ∀ u v w, (P u v w).coeff 0 = D u v w)
    (hdegree : ∀ u v w, (P u v w).degree ≤ K)
    (heval : ∀ t : O, IsUnit t →
      (fun u v w => (P u v w).eval t) ∈ LocalTensor.orbit T) :
    f (ofTensor D) ≤ f (ofTensor T) :=
  TensorSpectrum.TensorClass.Character.polynomial_constant_le f T D K
    (Separation.polynomial_power_mem_restrictionOrbit T D P K hconstant hdegree heval)

end TensorClass
end MatrixMultiplicationAllFields.MatrixExponent.Integral.Upper
