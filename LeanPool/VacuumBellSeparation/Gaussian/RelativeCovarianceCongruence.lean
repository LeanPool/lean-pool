/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixTraceNorm

/-!
# Orthogonal transport of relative covariance perturbations

For positive definite V and S V Sᵀ, the actual matrix
U=(S V Sᵀ)^(-1/2) S V^(1/2) is orthogonal. Relative perturbations are
conjugate by U, so their actual matrix trace norms agree. All inverse
square roots below are justified by positive definiteness.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Relative covariance perturbation given by `(CFC.sqrt V)⁻¹ * Δ * (CFC.sqrt V)⁻¹`. -/
def relativeCovariancePerturbation (V Δ : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt V)⁻¹ * Δ * (CFC.sqrt V)⁻¹

/-- Relative congruence orthogonal given by `(CFC.sqrt (S * V * Sᵀ))⁻¹ * S * CFC.sqrt V`. -/
def relativeCongruenceOrthogonal (S V : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt (S * V * Sᵀ))⁻¹ * S * CFC.sqrt V

theorem relativeCongruenceOrthogonal_mul_transpose
    (S : Matrix ι ι ℝ) {V : Matrix ι ι ℝ}
    (hV : V.PosDef) (hW : (S * V * Sᵀ).PosDef) :
    relativeCongruenceOrthogonal S V * (relativeCongruenceOrthogonal S V)ᵀ = 1 := by
  let R := CFC.sqrt V
  let Q := CFC.sqrt (S * V * Sᵀ)
  have hR := matrix_sqrt_posDef hV
  have hQ := matrix_sqrt_posDef hW
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hQit : (Q⁻¹)ᵀ = Q⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.inv.isHermitian.eq
  have hRR : R * R = V := CFC.sqrt_mul_sqrt_self V hV.posSemidef.nonneg
  have hQQ : Q * Q = S * V * Sᵀ := CFC.sqrt_mul_sqrt_self _ hW.posSemidef.nonneg
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hQiQ : Q⁻¹ * Q = 1 := Q.nonsing_inv_mul hQdet
  have hQQi : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQdet
  change (Q⁻¹ * S * R) * (Q⁻¹ * S * R)ᵀ = 1
  simp only [Matrix.transpose_mul, hRt, hQit]
  calc
    _ = Q⁻¹ * (S * (R * R) * Sᵀ) * Q⁻¹ := by noncomm_ring
    _ = Q⁻¹ * (Q * Q) * Q⁻¹ := by rw [hRR, hQQ]
    _ = (Q⁻¹ * Q) * (Q * Q⁻¹) := by noncomm_ring
    _ = 1 := by rw [hQiQ, hQQi, Matrix.one_mul]

theorem relativeCongruenceOrthogonal_transpose_mul
    (S : Matrix ι ι ℝ) {V : Matrix ι ι ℝ}
    (hV : V.PosDef) (hW : (S * V * Sᵀ).PosDef) :
    (relativeCongruenceOrthogonal S V)ᵀ * relativeCongruenceOrthogonal S V = 1 :=
  mul_eq_one_comm.mpr (relativeCongruenceOrthogonal_mul_transpose S hV hW)

/-- Literal orthogonal similarity of the actual normalized perturbations. -/
theorem relativeCovariancePerturbation_congruence
    (S : Matrix ι ι ℝ) {V : Matrix ι ι ℝ}
    (hV : V.PosDef) (hW : (S * V * Sᵀ).PosDef) (Δ : Matrix ι ι ℝ) :
    relativeCovariancePerturbation (S * V * Sᵀ) (S * Δ * Sᵀ) =
      relativeCongruenceOrthogonal S V * relativeCovariancePerturbation V Δ *
        (relativeCongruenceOrthogonal S V)ᵀ := by
  let R := CFC.sqrt V
  let Q := CFC.sqrt (S * V * Sᵀ)
  have hR := matrix_sqrt_posDef hV
  have hQ := matrix_sqrt_posDef hW
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hQit : (Q⁻¹)ᵀ = Q⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.inv.isHermitian.eq
  have hRdet : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hRiR : R⁻¹ * R = 1 := R.nonsing_inv_mul hRdet
  have hRRi : R * R⁻¹ = 1 := R.mul_nonsing_inv hRdet
  change Q⁻¹ * (S * Δ * Sᵀ) * Q⁻¹ =
    (Q⁻¹ * S * R) * (R⁻¹ * Δ * R⁻¹) * (Q⁻¹ * S * R)ᵀ
  simp only [Matrix.transpose_mul, hRt, hQit]
  calc
    _ = Q⁻¹ * S * Δ * Sᵀ * Q⁻¹ := by noncomm_ring
    _ = Q⁻¹ * S * (R * R⁻¹) * Δ * (R⁻¹ * R) * Sᵀ * Q⁻¹ := by
      rw [hRiR, hRRi, Matrix.mul_one, Matrix.mul_one]
    _ = _ := by noncomm_ring

theorem matrixTraceNorm_relativeCovariancePerturbation_congruence
    (S : Matrix ι ι ℝ) {V : Matrix ι ι ℝ}
    (hV : V.PosDef) (hW : (S * V * Sᵀ).PosDef) (Δ : Matrix ι ι ℝ) :
    matrixTraceNorm (relativeCovariancePerturbation (S * V * Sᵀ) (S * Δ * Sᵀ)) =
      matrixTraceNorm (relativeCovariancePerturbation V Δ) := by
  rw [relativeCovariancePerturbation_congruence S hV hW,
    matrixTraceNorm_orthogonal_conjugate _ (relativeCongruenceOrthogonal_transpose_mul S hV hW)]

end VacuumBellSeparation.Gaussian
