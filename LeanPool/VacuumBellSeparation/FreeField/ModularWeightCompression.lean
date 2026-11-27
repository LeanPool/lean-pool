/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCompression

/-!
# Compression of the bounded modular weight

The scalar function (1+x)^(1-p)(1-x)^p for 0<p<1 is used on the full
closed interval [-1,1]. Its compression inequality follows from the
proved weighted geometric-mean inequality for strict contractions and
norm-continuous functional calculus at the singular endpoints. No
bounded inverse is used at either endpoint.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap Gaussian Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Modular weight square function given by `(1 + x) ^ (1 - p) * (1 - x) ^ p`. -/
noncomputable def modularWeightSquareFunction (p x : ℝ) : ℝ :=
  (1 + x) ^ (1 - p) * (1 - x) ^ p

theorem continuous_modularWeightSquareFunction {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Continuous (modularWeightSquareFunction p) :=
  ((Real.continuous_rpow_const (sub_nonneg.mpr hp1)).comp
    (continuous_const.add continuous_id)).mul
      ((Real.continuous_rpow_const hp0).comp (continuous_const.sub continuous_id))

/-- The weighted mean agrees with the bounded scalar weight on strict contractions. -/
theorem weightedGeometricMean_eq_modularWeight (T : F →L[ℂ] F) (hT : IsSelfAdjoint T)
    (hnorm : ‖T‖ < 1) (p : ℝ) :
    weightedGeometricMean p (1 + T) (1 - T) = cfc (modularWeightSquareFunction p) T := by
  rw [← cfc_one_add_id T hT, ← cfc_one_sub_id T hT]
  have hplus (x : ℝ) (hx : x ∈ spectrum ℝ T) : 0 < 1 + x := by
    have hs := spectrum_mem_Ioo_of_norm_lt_one hnorm hx
    linarith [hs.1]
  have hminus (x : ℝ) (hx : x ∈ spectrum ℝ T) : 0 < 1 - x := by
    have hs := spectrum_mem_Ioo_of_norm_lt_one hnorm hx
    linarith [hs.2]
  rw [weightedGeometricMean_cfc T hT _ _ (by fun_prop) (by fun_prop) hplus hminus]
  apply cfc_congr
  intro x hx
  dsimp only
  rw [modularWeightSquareFunction, Real.rpow_sub (hplus x hx), Real.rpow_one,
    Real.div_rpow (hminus x hx).le (hplus x hx).le]
  ring

theorem modularWeight_compression_of_norm_lt_one (ι : E →ₗᵢ[ℂ] F)
    {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) (hnorm : ‖T‖ < 1)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    compression ι (cfc (modularWeightSquareFunction p) T) ≤
      cfc (modularWeightSquareFunction p) (compression ι T) := by
  rw [← weightedGeometricMean_eq_modularWeight T hT hnorm,
    ← weightedGeometricMean_eq_modularWeight (compression ι T)
      (compression_isSelfAdjoint ι hT) ((norm_compression_le ι T).trans_lt hnorm)]
  simpa only [compression_add, compression_sub, compression_one] using
    compression_weightedGeometricMean_le ι
      (one_add_isStrictlyPositive_of_norm_lt_one hT hnorm)
      (one_sub_isStrictlyPositive_of_norm_lt_one hT hnorm).nonneg hp0 hp1

/-- Norm convergence on the closed spectral interval, including spectra accumulating at ±1. -/
theorem tendsto_modularWeight_cfc_smul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1) :
    Tendsto (fun t : ℝ => cfc (modularWeightSquareFunction p) (t • T))
      (𝓝[<] (1 : ℝ)) (𝓝 (cfc (modularWeightSquareFunction p) T)) := by
  have hspec : spectrum ℝ T ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun _ hx => spectrum_mem_Icc_of_norm_le_one hnorm hx
  have hc := continuousOn_cfc (F →L[ℂ] F) (s := Set.Icc (-1 : ℝ) 1) isCompact_Icc
    (modularWeightSquareFunction p) (continuous_modularWeightSquareFunction hp0 hp1).continuousOn
  have hlim : Tendsto (fun t : ℝ => t • T) (𝓝[<] (1 : ℝ)) (𝓝 T) := by
    have hcont : Continuous (fun t : ℝ => t • T) := continuous_id.smul continuous_const
    simpa using (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  apply (hc T ⟨hT, hspec⟩).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hlim, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact ⟨(show IsSelfAdjoint t by cfc_tac).smul hT,
    fun _ hx => spectrum_mem_Icc_of_norm_le_one (norm_smul_lt_one hnorm ht).le hx⟩

/-- The full closed-contraction compression inequality for the source modular weight. -/
theorem modularWeight_compression (ι : E →ₗᵢ[ℂ] F)
    {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1) :
    compression ι (cfc (modularWeightSquareFunction p) T) ≤
      cfc (modularWeightSquareFunction p) (compression ι T) := by
  have hleft := (continuous_compression ι).continuousAt.tendsto.comp
    (tendsto_modularWeight_cfc_smul hp0.le hp1 hT hnorm)
  have hright := tendsto_modularWeight_cfc_smul hp0.le hp1
    (compression_isSelfAdjoint ι hT) ((norm_compression_le ι T).trans hnorm)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  simpa only [compression_real_smul, Function.comp_apply]
    using modularWeight_compression_of_norm_lt_one ι
    ((show IsSelfAdjoint t by cfc_tac).smul hT) (norm_smul_lt_one hnorm ht) hp0 hp1

end VacuumBellSeparation
