/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.TraceNormCompression
public import LeanPool.VacuumBellSeparation.Gaussian.NormalizedCommutation

/-!
# Reserve lower bounds control the actual normalized perturbation

For a positive invertible finite target weight H, a lower bound
c iota† R² iota <= H constructs the actual rectangular map
A=R iota H^(-1/2), with ||A||² <= c^(-1). A full-space factorization
D=R Y R therefore gives the actual normalized compression A† Y A.
Neither the full reserve R nor the full perturbation Y is inverted.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Reserve normalization map given by `R.comp (ι.toContinuousLinearMap.comp (H ^ (-(1 / 2) :
ℝ)))`. -/
def reserveNormalizationMap (ι : E →ₗᵢ[ℂ] F)
    (R : F →L[ℂ] F) (H : E →L[ℂ] E) : E →L[ℂ] F :=
  R.comp (ι.toContinuousLinearMap.comp (H ^ (-(1 / 2) : ℝ)))

/-- Normalized reserve compression given by `H ^ (-(1 / 2) : ℝ) * compression ι D * H ^ (-(1 / 2) :
ℝ)`. -/
def normalizedReserveCompression (ι : E →ₗᵢ[ℂ] F)
    (D : F →L[ℂ] F) (H : E →L[ℂ] E) : E →L[ℂ] E :=
  H ^ (-(1 / 2) : ℝ) * compression ι D * H ^ (-(1 / 2) : ℝ)

theorem reserveNormalizationMap_gram (ι : E →ₗᵢ[ℂ] F)
    {R : F →L[ℂ] F} (hR : IsSelfAdjoint R) (H : E →L[ℂ] E) :
    (reserveNormalizationMap ι R H).adjoint.comp (reserveNormalizationMap ι R H) =
      normalizedReserveCompression ι (R * R) H := by
  have hN : (H ^ (-(1 / 2) : ℝ)).adjoint = H ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg (a := H) (y := -(1 / 2 : ℝ))).isSelfAdjoint.adjoint_eq
  simp only [reserveNormalizationMap, normalizedReserveCompression, compression,
    adjoint_comp, hR.adjoint_eq, hN, mul_def, comp_assoc]

theorem reserveNormalizationMap_factorization (ι : E →ₗᵢ[ℂ] F)
    {R : F →L[ℂ] F} (hR : IsSelfAdjoint R)
    (Y : F →L[ℂ] F) (H : E →L[ℂ] E) :
    normalizedReserveCompression ι (R * Y * R) H =
      (reserveNormalizationMap ι R H).adjoint.comp
        (Y.comp (reserveNormalizationMap ι R H)) := by
  have hN : (H ^ (-(1 / 2) : ℝ)).adjoint = H ^ (-(1 / 2) : ℝ) :=
    (CFC.rpow_nonneg (a := H) (y := -(1 / 2 : ℝ))).isSelfAdjoint.adjoint_eq
  simp only [reserveNormalizationMap, normalizedReserveCompression, compression,
    adjoint_comp, hR.adjoint_eq, hN, mul_def, comp_assoc]

theorem reserveNormalizationMap_norm_sq_le (ι : E →ₗᵢ[ℂ] F)
    {R : F →L[ℂ] F} (hR : IsSelfAdjoint R)
    {H : E →L[ℂ] E} (hH : IsStrictlyPositive H)
    {c : ℝ} (hc : 0 < c) (hlower : c • compression ι (R * R) ≤ H) :
    ‖reserveNormalizationMap ι R H‖ ^ 2 ≤ c⁻¹ := by
  let A := reserveNormalizationMap ι R H
  have hN : IsSelfAdjoint (H ^ (-(1 / 2) : ℝ)) := CFC.rpow_nonneg.isSelfAdjoint
  have hbound : c • (A.adjoint.comp A) ≤ 1 := by
    have h := hN.conjugate_le_conjugate hlower
    rw [CFC.conjugate_rpow_neg_one_half H hH] at h
    simpa only [A, reserveNormalizationMap_gram ι hR,
      normalizedReserveCompression, mul_smul_comm, smul_mul_assoc] using h
  have hp : 0 ≤ A.adjoint.comp A := by
    exact nonneg_iff_isPositive.mpr (isPositive_adjoint_comp_self A)
  have hn := (CStarAlgebra.norm_le_one_iff_of_nonneg
    (c • (A.adjoint.comp A)) (smul_nonneg hc.le hp)).mpr hbound
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, norm_adjoint_comp_self] at hn
  change ‖A‖ ^ 2 ≤ c⁻¹
  rw [← one_div, le_div_iff₀ hc]
  simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using hn

theorem norm_normalizedReserveCompression_le (ι : E →ₗᵢ[ℂ] F)
    {R : F →L[ℂ] F} (hR : IsSelfAdjoint R)
    {H : E →L[ℂ] E} (hH : IsStrictlyPositive H)
    {c : ℝ} (hc : 0 < c) (hlower : c • compression ι (R * R) ≤ H)
    (Y : F →L[ℂ] F) :
    ‖normalizedReserveCompression ι (R * Y * R) H‖ ≤ c⁻¹ * ‖Y‖ := by
  rw [reserveNormalizationMap_factorization ι hR]
  let A := reserveNormalizationMap ι R H
  calc
    ‖A.adjoint.comp (Y.comp A)‖ ≤ ‖A.adjoint‖ * (‖Y‖ * ‖A‖) :=
      (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖A‖ ^ 2 * ‖Y‖ := by rw [adjoint.norm_map]; ring
    _ ≤ c⁻¹ * ‖Y‖ := mul_le_mul_of_nonneg_right
      (reserveNormalizationMap_norm_sq_le ι hR hH hc hlower) (norm_nonneg _)

theorem operatorTraceNorm_normalizedReserveCompression_le (ι : E →ₗᵢ[ℂ] F)
    {R : F →L[ℂ] F} (hR : IsSelfAdjoint R)
    {H : E →L[ℂ] E} (hH : IsStrictlyPositive H)
    {c : ℝ} (hc : 0 < c) (hlower : c • compression ι (R * R) ≤ H)
    {Y : F →L[ℂ] F} (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    operatorTraceNorm (normalizedReserveCompression ι (R * Y * R) H) ≤
      ENNReal.ofReal c⁻¹ * operatorTraceNorm Y := by
  rw [reserveNormalizationMap_factorization ι hR]
  exact (operatorTraceNorm_adjoint_sandwich_le hcY hY _).trans
    (_root_.mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (reserveNormalizationMap_norm_sq_le ι hR hH hc hlower)) _)

end VacuumBellSeparation.Gaussian
