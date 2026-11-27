/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ReserveNormalization
public import LeanPool.VacuumBellSeparation.Gaussian.CompressionPower

/-!
# Thermal normalization of the source reserve factorizations

The proved high- and low-compression inequalities supply the lower weight
bound used by ReserveNormalization. Thus a genuine full-space reserve
factorization controls both norms of the normalized finite perturbation.
Only the target thermal weight is required to be strictly positive; the
full commutation operator may have spectrum at either endpoint.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem reserve_rpow_mul_self (B : F →L[ℂ] F) {a : ℝ} (ha : 0 ≤ a) :
    reserve B ^ a * reserve B ^ a = reserve B ^ (2 * a) := by
  have hR : 0 ≤ reserve B := CFC.sqrt_nonneg (1 - B ^ 2)
  rw [← positiveOperator_rpow_add_nonneg hR ha ha]
  congr 1
  ring

theorem thermal_low_reserve_lower_bound (ι : E →ₗᵢ[ℂ] F)
    {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1 / 2) :
    thermalConst a • compression ι (reserve B ^ a * reserve B ^ a) ≤
      normalizedThermal a (compression ι B) := by
  have ha1 : a < 1 := by linarith
  rw [reserve_rpow_mul_self B ha₀.le]
  have hlow := smul_le_smul_of_nonneg_left (low_compression ι hB hnorm ha₀ ha₁)
    (thermalConst_pos ha₀ ha1).le
  have hc := thermal_comparison_signed ha₀ ha1
    (compression_isSelfAdjoint ι hB) ((norm_compression_le ι B).trans hnorm)
  rw [← normalizedThermal_eq_cfc_abs ha₀ (compression_isSelfAdjoint ι hB)
    ((norm_compression_le ι B).trans hnorm)] at hc
  exact hlow.trans hc

theorem thermal_high_reserve_lower_bound (ι : E →ₗᵢ[ℂ] F)
    {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) (n : ℕ) :
    let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
    thermalConst b • compression ι (reserve B ^ b * reserve B ^ b) ≤
      normalizedThermal b (compression ι B) := by
  dsimp only
  rw [reserve_rpow_mul_self B (by positivity)]
  exact (normalizedThermal_compression_chain ι hB hnorm n).1.trans
    (normalizedThermal_compression_chain ι hB hnorm n).2

theorem low_thermal_normalized_factorization_bounds (ι : E →ₗᵢ[ℂ] F)
    {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1 / 2)
    (hH : IsStrictlyPositive (normalizedThermal a (compression ι B)))
    {Y : F →L[ℂ] F} (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    let Z := normalizedReserveCompression ι (reserve B ^ a * Y * reserve B ^ a)
      (normalizedThermal a (compression ι B))
    ‖Z‖ ≤ (thermalConst a)⁻¹ * ‖Y‖ ∧
      operatorTraceNorm Z ≤ ENNReal.ofReal (thermalConst a)⁻¹ * operatorTraceNorm Y := by
  dsimp only
  have hc := thermalConst_pos ha₀ (show a < 1 by linarith)
  have hl := thermal_low_reserve_lower_bound ι hB hnorm ha₀ ha₁
  have hR : IsSelfAdjoint (reserve B ^ a) := CFC.rpow_nonneg.isSelfAdjoint
  exact ⟨norm_normalizedReserveCompression_le ι hR hH hc hl Y,
    operatorTraceNorm_normalizedReserveCompression_le ι hR hH hc hl hcY hY⟩

theorem high_thermal_normalized_factorization_bounds (ι : E →ₗᵢ[ℂ] F)
    {B : F →L[ℂ] F} (hB : IsSelfAdjoint B) (hnorm : ‖B‖ ≤ 1) (n : ℕ)
    (hH : IsStrictlyPositive (normalizedThermal
      (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) (compression ι B)))
    {Y : F →L[ℂ] F} (hcY : IsCompactOperator Y) (hY : IsSelfAdjoint Y) :
    let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
    let Z := normalizedReserveCompression ι (reserve B ^ b * Y * reserve B ^ b)
      (normalizedThermal b (compression ι B))
    ‖Z‖ ≤ (thermalConst b)⁻¹ * ‖Y‖ ∧
      operatorTraceNorm Z ≤ ENNReal.ofReal (thermalConst b)⁻¹ * operatorTraceNorm Y := by
  dsimp only
  have hb₀ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hb₁ : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact_mod_cast (show n + 1 < n + 2 by omega)
  have hc := thermalConst_pos hb₀ hb₁
  have hl := thermal_high_reserve_lower_bound ι hB hnorm n
  have hR : IsSelfAdjoint (reserve B ^ (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))) :=
    CFC.rpow_nonneg.isSelfAdjoint
  exact ⟨norm_normalizedReserveCompression_le ι hR hH hc hl Y,
    operatorTraceNorm_normalizedReserveCompression_le ι hR hH hc hl hcY hY⟩

end VacuumBellSeparation.Gaussian
