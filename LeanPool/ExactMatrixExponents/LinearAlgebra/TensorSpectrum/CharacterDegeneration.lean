/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassPowers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagGrowth

/-!
# Character monotonicity under polynomial restriction

A linear number of copies in a tensor-power bound disappears after taking
the limit. The finite interpolation proof supplies that bound.
-/

@[expose] public section

noncomputable section

open scoped NNReal
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation
open MatrixMultiplicationAllFields.MatrixExponent

namespace MatrixMultiplicationAllFields.TensorSpectrum.TensorClass

variable {R : Type*} [CommSemiring R]

theorem Character.polynomial_constant_le (f : Character R)
    {X Y Z U V W : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor R X Y Z) (D : Tensor R U V W) (K : ℕ)
    (hrestrict : ∀ j : ℕ, Tensor.power D j ∈ LocalTensor.orbit
      (Tensor.directSum (fun _ : Fin (K * j + 1) => Tensor.power T j))) :
    f (ofTensor D) ≤ f (ofTensor T) := by
  have hpower : ∀ j : ℕ,
      (f (ofTensor D)) ^ j ≤ (K * j + 1 : ℝ≥0) * (f (ofTensor T)) ^ j := by
    intro j
    have hr := hrestrict j
    have hmono := f.monotone' (ofTensor_le hr)
    simpa only [Character.map_directSum_const, Character.map_power_tensor,
      Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hmono
  have hreal := le_of_pow_le_linear_mul_pow
    (f (ofTensor T) : ℝ) (f (ofTensor D) : ℝ) (K : ℝ)
    (f (ofTensor T)).coe_nonneg
    (fun j => by exact_mod_cast hpower j)
  exact_mod_cast hreal

end MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
