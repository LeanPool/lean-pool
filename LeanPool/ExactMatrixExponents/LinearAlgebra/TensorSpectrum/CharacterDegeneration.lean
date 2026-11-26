/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TensorClassPowers
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.TagGrowth
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.PolynomialTensors

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

open PolynomialTensors (polynomialTensor)

/-- The coefficient at the constant input monomials is one. -/
theorem Character.polynomial_value_pos (f : Character R) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < (f (ofTensor (polynomialTensor a b)) : ℝ) := by
  have hunit : ∃ i j k, polynomialTensor (K := R) a b i j k = 1 :=
    ⟨⟨0, by omega⟩, ⟨0, by omega⟩, ⟨0, by omega⟩, by simp [polynomialTensor]⟩
  have h := f.monotone' (ofTensor_le (CoefficientTensor.unit_restricts_natTensor_one hunit))
  have hone : ofTensor (CoefficientTensor.natTensor 1) = (1 : TensorClass R) := by
    simpa only [Nat.cast_one] using (natCast_eq_ofTensor_natTensor 1).symm
  have hnn : 1 ≤ f (ofTensor (polynomialTensor a b)) := calc
    1 = f.toHom (ofTensor (CoefficientTensor.natTensor 1)) := by
      rw [hone]
      exact f.toHom.map_one.symm
    _ ≤ f.toHom (ofTensor (polynomialTensor a b)) := h
  have hr : (1 : ℝ) ≤ f (ofTensor (polynomialTensor a b)) := by exact_mod_cast hnn
  exact zero_lt_one.trans_le hr

theorem Character.polynomial_value_le_of_rankAtMost (f : Character R) (a b : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Tensor.RankAtMost (polynomialTensor (K := R) a b) (a + b - 1)) :
    (f (ofTensor (polynomialTensor a b)) : ℝ) ≤ (a : ℝ) + (b : ℝ) - 1 := by
  have hRank : rank (ofTensor (polynomialTensor (K := R) a b)) ≤ a + b - 1 := by
    rw [rank_ofTensor]
    exact (CoefficientTensor.rank_le_iff _ _).mpr h
  have hnn : f (ofTensor (polynomialTensor a b)) ≤ (a + b - 1 : ℕ) :=
    (f.le_rank _).trans (Nat.cast_le.mpr hRank)
  have hr : (f (ofTensor (polynomialTensor a b)) : ℝ) ≤ ((a + b - 1 : ℕ) : ℝ) := by
    exact_mod_cast hnn
  have hab : 1 ≤ a + b := by omega
  simpa only [Nat.cast_sub hab, Nat.cast_add, Nat.cast_one] using hr

end MatrixMultiplicationAllFields.TensorSpectrum.TensorClass
