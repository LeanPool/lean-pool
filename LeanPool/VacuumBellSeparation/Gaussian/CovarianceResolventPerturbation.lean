/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixResolventBounds
public import LeanPool.VacuumBellSeparation.Gaussian.RelativeCovarianceCongruence
public import LeanPool.VacuumBellSeparation.Gaussian.SandwichAlgebra

/-!
# Actual covariance perturbations as resolvent sandwiches

The source covariance difference L(H-Δ)⁻¹L-LH⁻¹L is expressed through
Z=H^(-1/2)ΔH^(-1/2) and the genuine resolvent (I-Z)⁻¹-I. Normalizing by
a second positive covariance gives B[(I-Z)⁻¹-I]Bᵀ with an explicit B.
The resulting operator/trace norm estimates are proved, rather than
assumed as fields of a covariance perturbation structure.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Inverse sandwich perturbation given by `L * (H - Δ)⁻¹ * L - L * H⁻¹ * L`. -/
def inverseSandwichPerturbation (H L Δ : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  L * (H - Δ)⁻¹ * L - L * H⁻¹ * L

/-- Covariance perturbation multiplier given by `(CFC.sqrt V)⁻¹ * L * (CFC.sqrt H)⁻¹`. -/
def covariancePerturbationMultiplier (V H L : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (CFC.sqrt V)⁻¹ * L * (CFC.sqrt H)⁻¹

theorem relativeCovariancePerturbation_isHermitian
    {H Δ : Matrix ι ι ℝ} (hH : H.PosDef) (hΔ : Δ.IsHermitian) :
    (relativeCovariancePerturbation H Δ).IsHermitian := by
  have hi : ((CFC.sqrt H)⁻¹)ᵀ = (CFC.sqrt H)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hH).inv.isHermitian.eq
  simpa only [relativeCovariancePerturbation,
    Matrix.conjTranspose_eq_transpose_of_trivial, hi] using
    Matrix.isHermitian_mul_mul_conjTranspose (CFC.sqrt H)⁻¹ hΔ

theorem covariance_gap_factorization {H : Matrix ι ι ℝ} (hH : H.PosDef) (Δ : Matrix ι ι ℝ) :
    H - Δ = CFC.sqrt H * (1 - relativeCovariancePerturbation H Δ) * CFC.sqrt H := by
  have h := perturbation_factorization (CFC.sqrt H) Δ (matrix_sqrt_posDef hH).isUnit
  rw [CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg] at h
  exact h

theorem covariance_gap_posDef_of_relative_norm
    {H Δ : Matrix ι ι ℝ} (hH : H.PosDef) (hΔ : Δ.IsHermitian)
    (hδ : ‖relativeCovariancePerturbation H Δ‖ < 1) : (H - Δ).PosDef := by
  have hR := matrix_sqrt_posDef hH
  have hp := matrix_one_sub_posDef_of_norm_lt_one
    (relativeCovariancePerturbation_isHermitian hH hΔ) hδ
  have h := hR.isUnit.posDef_star_right_conjugate_iff.mpr hp
  simpa only [Matrix.star_eq_conjTranspose, hR.isHermitian.eq,
    ← covariance_gap_factorization hH Δ] using h

theorem inverseSandwichPerturbation_resolvent
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (L Δ : Matrix ι ι ℝ) :
    inverseSandwichPerturbation H L Δ =
      (L * (CFC.sqrt H)⁻¹) * matrixResolventPerturbation (relativeCovariancePerturbation H Δ) *
        ((CFC.sqrt H)⁻¹ * L) := by
  have hHinv : H⁻¹ = (CFC.sqrt H)⁻¹ * (CFC.sqrt H)⁻¹ := by
    calc
      H⁻¹ = (CFC.sqrt H * CFC.sqrt H)⁻¹ :=
        congrArg (fun M : Matrix ι ι ℝ => M⁻¹)
          (CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg).symm
      _ = _ := Matrix.mul_inv_rev _ _
  rw [inverseSandwichPerturbation, covariance_gap_factorization hH Δ,
    Matrix.mul_inv_rev, Matrix.mul_inv_rev, hHinv, matrixResolventPerturbation]
  noncomm_ring

theorem relative_inverseSandwichPerturbation_eq
    {V H L : Matrix ι ι ℝ} (hV : V.PosDef) (hH : H.PosDef) (hL : L.IsHermitian)
    (Δ : Matrix ι ι ℝ) :
    relativeCovariancePerturbation V (inverseSandwichPerturbation H L Δ) =
      covariancePerturbationMultiplier V H L *
        matrixResolventPerturbation (relativeCovariancePerturbation H Δ) *
          (covariancePerturbationMultiplier V H L)ᵀ := by
  have hVi : ((CFC.sqrt V)⁻¹)ᵀ = (CFC.sqrt V)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hV).inv.isHermitian.eq
  have hHi : ((CFC.sqrt H)⁻¹)ᵀ = (CFC.sqrt H)⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (matrix_sqrt_posDef hH).inv.isHermitian.eq
  have hLt : Lᵀ = L := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hL.eq
  rw [relativeCovariancePerturbation, inverseSandwichPerturbation_resolvent hH L Δ]
  simp only [covariancePerturbationMultiplier, Matrix.transpose_mul, hVi, hHi, hLt]
  noncomm_ring

theorem norm_relative_inverseSandwichPerturbation_le
    {V H L Δ : Matrix ι ι ℝ} (hV : V.PosDef) (hH : H.PosDef) (hL : L.IsHermitian)
    (hΔ : Δ.IsHermitian) (hδ : ‖relativeCovariancePerturbation H Δ‖ < 1) :
    ‖relativeCovariancePerturbation V (inverseSandwichPerturbation H L Δ)‖ ≤
      ‖covariancePerturbationMultiplier V H L‖ ^ 2 *
        (‖relativeCovariancePerturbation H Δ‖ / (1 - ‖relativeCovariancePerturbation H Δ‖)) := by
  let B := covariancePerturbationMultiplier V H L
  let Z := relativeCovariancePerturbation H Δ
  have ht : ‖Bᵀ‖ = ‖B‖ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose B
  rw [relative_inverseSandwichPerturbation_eq hV hH hL Δ]
  calc
    ‖B * matrixResolventPerturbation Z * Bᵀ‖ ≤
        ‖B‖ * ‖matrixResolventPerturbation Z‖ * ‖Bᵀ‖ := norm_mul₃_le
    _ = ‖B‖ ^ 2 * ‖matrixResolventPerturbation Z‖ := by rw [ht]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (norm_matrixResolventPerturbation_le (relativeCovariancePerturbation_isHermitian hH hΔ) hδ)
      (sq_nonneg _)

theorem matrixTraceNorm_relative_inverseSandwichPerturbation_le
    {V H L Δ : Matrix ι ι ℝ} (hV : V.PosDef) (hH : H.PosDef) (hL : L.IsHermitian)
    (hΔ : Δ.IsHermitian) (hδ : ‖relativeCovariancePerturbation H Δ‖ < 1) :
    matrixTraceNorm (relativeCovariancePerturbation V (inverseSandwichPerturbation H L Δ)) ≤
      ‖covariancePerturbationMultiplier V H L‖ ^ 2 *
        ((1 - ‖relativeCovariancePerturbation H Δ‖)⁻¹ *
          matrixTraceNorm (relativeCovariancePerturbation H Δ)) := by
  rw [relative_inverseSandwichPerturbation_eq hV hH hL Δ]
  exact (matrixTraceNorm_sandwich_le
    (matrixResolventPerturbation_isHermitian (relativeCovariancePerturbation_isHermitian hH hΔ))
      (covariancePerturbationMultiplier V H L)).trans
    (mul_le_mul_of_nonneg_left
      (matrixTraceNorm_matrixResolventPerturbation_le
        (relativeCovariancePerturbation_isHermitian hH hΔ) hδ) (sq_nonneg _))

end VacuumBellSeparation.Gaussian
