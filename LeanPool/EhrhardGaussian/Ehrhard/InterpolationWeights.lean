/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-! The diagonal interpolation matrix represents a weighted sum of squared normalized gradients. -/

@[expose] public noncomputable section

open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal interpolation matrix has entries ωᵢvᵢ/Iᵢ². -/
def interpolationWeightMatrix (ω v I : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal (fun i => ω i * v i / (I i) ^ 2)

/-- The interpolation weight matrix has the stated weighted diagonal quadratic form. -/
theorem interpolationWeightMatrix_quadratic (ω v I z : ι → ℝ) :
    z ⬝ᵥ (interpolationWeightMatrix ω v I *ᵥ z) =
      ∑ i, ω i * (v i * (z i) ^ 2 / (I i) ^ 2) := by
  simp only [interpolationWeightMatrix, dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring


/-- Squared componentwise gradient bounds control `zᵀDz`; the covariance
variances occur once. -/
theorem interpolationWeightMatrix_quadratic_le {ω v I z : ι → ℝ} {K : ℝ}
    (hω : ∀ i, 0 ≤ ω i) (hsum : ∑ i, ω i = 1) (hI : ∀ i, I i ≠ 0)
    (hcomponent : ∀ i, v i * (z i) ^ 2 ≤ (I i) ^ 2 / K) :
    z ⬝ᵥ (interpolationWeightMatrix ω v I *ᵥ z) ≤ 1 / K := by
  rw [interpolationWeightMatrix_quadratic]
  calc
    (∑ i, ω i * (v i * (z i) ^ 2 / (I i) ^ 2)) ≤ ∑ i, ω i * (1 / K) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hω i)
      apply (div_le_iff₀ (sq_pos_of_ne_zero (hI i))).mpr
      exact (hcomponent i).trans_eq (by ring)
    _ = 1 / K := by rw [← Finset.sum_mul, hsum, one_mul]

end EhrhardGaussian.Ehrhard

end
