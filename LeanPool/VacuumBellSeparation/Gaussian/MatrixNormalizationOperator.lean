/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.RealMatrixOperatorNorms
public import LeanPool.VacuumBellSeparation.Gaussian.ReserveNormalization

/-!
# Matrix inverse-square-root normalization is the actual operator power

Every inverse here is justified by finite positive definiteness. The
actual matrix normalized perturbation is identified with the bounded
operator expression H^(-1/2) D H^(-1/2), rather than defined to stand in
for it. This joins the matrix Gaussian estimate to source compression.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem realMatrixOperator_mul (A B : Matrix ι ι ℝ) :
    realMatrixOperator (A * B) = realMatrixOperator A * realMatrixOperator B := by
  simp only [realMatrixOperator, complexifyMatrix_mul, map_mul]

@[simp] theorem realMatrixOperator_one :
    realMatrixOperator (1 : Matrix ι ι ℝ) = 1 := by
  simp only [realMatrixOperator, complexifyMatrix_one, map_one]

theorem realMatrixOperator_isStrictlyPositive {H : Matrix ι ι ℝ} (hH : H.PosDef) :
    IsStrictlyPositive (realMatrixOperator H) := by
  have hp := complexifyMatrix_posDef hH
  exact (hp.isUnit.map (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toMonoidHom).isStrictlyPositive
    (map_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) hp.posSemidef.nonneg)

theorem realMatrixOperator_sqrt {H : Matrix ι ι ℝ} (hH : H.PosSemidef) :
    realMatrixOperator (CFC.sqrt H) = CFC.sqrt (realMatrixOperator H) := by
  rw [realMatrixOperator, complexifyMatrix_sqrt hH,
    toEuclideanCLM_sqrt (complexifyMatrix_posSemidef hH)]
  rfl

theorem realMatrixOperator_inverse_sqrt {H : Matrix ι ι ℝ} (hH : H.PosDef) :
    realMatrixOperator ((CFC.sqrt H)⁻¹) = realMatrixOperator H ^ (-(1 / 2) : ℝ) := by
  let R := realMatrixOperator (CFC.sqrt H)
  let L := realMatrixOperator ((CFC.sqrt H)⁻¹)
  let N := realMatrixOperator H ^ (-(1 / 2) : ℝ)
  have hdet := (Matrix.isUnit_iff_isUnit_det (CFC.sqrt H)).mp (matrix_sqrt_posDef hH).isUnit
  have hLR : L * R = 1 := by
    dsimp only [L, R]
    rw [← realMatrixOperator_mul, Matrix.nonsing_inv_mul _ hdet, realMatrixOperator_one]
  have hRN : R * N = 1 := by
    dsimp only [R, N]
    rw [realMatrixOperator_sqrt hH.posSemidef, CFC.sqrt_eq_rpow]
    exact CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) (realMatrixOperator_isStrictlyPositive hH)
  change L = N
  calc
    L = L * (R * N) := by rw [hRN, mul_one]
    _ = N := by rw [← mul_assoc, hLR, one_mul]

theorem realMatrixOperator_relativeCovariancePerturbation
    {H : Matrix ι ι ℝ} (hH : H.PosDef) (D : Matrix ι ι ℝ) :
    realMatrixOperator (relativeCovariancePerturbation H D) =
      realMatrixOperator H ^ (-(1 / 2) : ℝ) * realMatrixOperator D *
        realMatrixOperator H ^ (-(1 / 2) : ℝ) := by
  rw [relativeCovariancePerturbation, realMatrixOperator_mul, realMatrixOperator_mul,
    realMatrixOperator_inverse_sqrt hH]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem realMatrixOperator_normalized_compression
    (e : EuclideanSpace ℂ ι →ₗᵢ[ℂ] F)
    {H D : Matrix ι ι ℝ} (hH : H.PosDef)
    {T : F →L[ℂ] F} (hD : realMatrixOperator D = compression e T) :
    realMatrixOperator (relativeCovariancePerturbation H D) =
      normalizedReserveCompression e T (realMatrixOperator H) := by
  rw [realMatrixOperator_relativeCovariancePerturbation hH D, hD]
  rfl

theorem matrix_normalized_compression_norms
    (e : EuclideanSpace ℂ ι →ₗᵢ[ℂ] F)
    {H D : Matrix ι ι ℝ} (hH : H.PosDef)
    {T : F →L[ℂ] F} (hD : realMatrixOperator D = compression e T) :
    ‖relativeCovariancePerturbation H D‖ =
        ‖normalizedReserveCompression e T (realMatrixOperator H)‖ ∧
      ENNReal.ofReal (matrixTraceNorm (relativeCovariancePerturbation H D)) =
        operatorTraceNorm (normalizedReserveCompression e T (realMatrixOperator H)) := by
  have he := realMatrixOperator_normalized_compression e hH hD
  constructor
  · rw [← he, norm_realMatrixOperator]
  · rw [← he, operatorTraceNorm_realMatrixOperator]

end VacuumBellSeparation.Gaussian
