/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.InterpolationWeights
public import Mathlib.LinearAlgebra.Matrix.Hadamard

/-! # The sufficient sign implication for time-dependent interpolation -/

@[expose] public noncomputable section

open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The matrix condition and gradient bound imply the lower bound `c` on the Hessian quadratic form.
-/
theorem corrected_interpolation_quadratic_nonneg {ι : Type*} [Fintype ι]
    {H D : Matrix ι ι ℝ} {c K : ℝ} (hc : c ≤ 0) (hK : 0 < K)
    (hPSD : (H - (K * c) • D).PosSemidef) (v : ι → ℝ)
    (hv : v ⬝ᵥ (D *ᵥ v) ≤ 1 / K) : c ≤ v ⬝ᵥ (H *ᵥ v) := by
  have hmatrix := hPSD.dotProduct_mulVec_nonneg v
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul] at hmatrix
  have hscale : K * (v ⬝ᵥ (D *ᵥ v)) ≤ 1 := by
    have h := (le_div_iff₀ hK).mp hv
    simpa only [mul_comm] using h
  have htime := mul_le_mul_of_nonpos_left hscale hc
  nlinarith only [hmatrix, htime]

/-- The positive semidefinite Hessian bound gives the required nonpositive interpolation derivative.
-/
theorem corrected_interpolation_sign {ι : Type*} [Fintype ι]
    {H D : Matrix ι ι ℝ} {c K : ℝ} (hc : c ≤ 0) (hK : 0 < K)
    (hPSD : (H - (K * c) • D).PosSemidef) (v : ι → ℝ)
    (hv : v ⬝ᵥ (D *ᵥ v) ≤ 1 / K) : c - v ⬝ᵥ (H *ᵥ v) ≤ 0 :=
  sub_nonpos.mpr (corrected_interpolation_quadratic_nonneg hc hK hPSD v hv)

/-- Pulling a correlated family back to independent Gaussian coordinates
produces precisely the covariance-weighted Hessian quadratic form. -/
theorem gram_hessian_contraction {ι α : Type*} [Fintype ι] [Fintype α]
    (C : Matrix ι α ℝ) (H : Matrix ι ι ℝ) (d : ι → ℝ) :
    (∑ i, ∑ l, H i l * ∑ j, (d i * C i j) * (d l * C l j)) =
      d ⬝ᵥ (((C * Cᵀ) ⊙ H) *ᵥ d) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

end EhrhardGaussian.Ehrhard

end
