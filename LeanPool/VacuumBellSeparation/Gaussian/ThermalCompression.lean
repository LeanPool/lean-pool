/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# High thermal compression at singular endpoints

The strict thermal compression theorem is extended to contractions by
`t T`, with `0<t<1`, and norm-continuity of the thermal functional calculus.
The totalized inverse-sum expression is never evaluated at singular inputs.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Filter Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem spectrum_mem_Icc_of_norm_le_one {T : F →L[ℂ] F} (hT : ‖T‖ ≤ 1)
    {x : ℝ} (hx : x ∈ spectrum ℝ T) : x ∈ Set.Icc (-1 : ℝ) 1 := by
  rcases subsingleton_or_nontrivial F with hF | hF
  · let := hF
    simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hx
  · let := hF
    exact abs_le.mp (by simpa only [Real.norm_eq_abs] using
      (spectrum.norm_le_norm_of_mem hx).trans hT)

theorem continuousOn_thermalIncrement_abs {b : ℝ} (hb : 0 < b) :
    ContinuousOn (fun x : ℝ => thermalIncrement b |x|) (Set.Icc (-1 : ℝ) 1) := by
  apply (continuousOn_thermalIncrement hb).comp continuous_abs.continuousOn
  intro x hx
  exact ⟨abs_nonneg x, abs_le.mpr hx⟩

omit [CompleteSpace F] in
theorem norm_smul_lt_one {T : F →L[ℂ] F} (hT : ‖T‖ ≤ 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) : ‖t • T‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
  exact (mul_le_mul_of_nonneg_left hT ht.1.le).trans_lt (by simpa using ht.2)

theorem tendsto_thermal_cfc_smul {b : ℝ} (hb : 0 < b)
    {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1) :
    Tendsto (fun t : ℝ => cfc (fun x : ℝ => thermalIncrement b |x|) (t • T))
      (𝓝[<] (1 : ℝ)) (𝓝 (cfc (fun x : ℝ => thermalIncrement b |x|) T)) := by
  have hspec : spectrum ℝ T ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun _ hx => spectrum_mem_Icc_of_norm_le_one hnorm hx
  have hc := continuousOn_cfc (F →L[ℂ] F) isCompact_Icc
    (fun x : ℝ => thermalIncrement b |x|) (continuousOn_thermalIncrement_abs hb)
  have hlim : Tendsto (fun t : ℝ => t • T) (𝓝[<] (1 : ℝ)) (𝓝 T) := by
    have hcont : Continuous (fun t : ℝ => t • T) := continuous_id.smul continuous_const
    simpa using (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  apply (hc T ⟨hT, hspec⟩).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hlim, ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  exact ⟨(show IsSelfAdjoint t by cfc_tac).smul hT,
    fun _ hx => spectrum_mem_Icc_of_norm_le_one (norm_smul_lt_one hnorm ht).le hx⟩

theorem continuous_compression (ι : E →ₗᵢ[ℂ] F) :
    Continuous (compression ι) := by
  change Continuous (fun A : F →L[ℂ] F =>
    (ι.toContinuousLinearMap.adjoint.comp A).comp ι.toContinuousLinearMap)
  exact ((continuous_const : Continuous (fun _ : F →L[ℂ] F =>
    ι.toContinuousLinearMap.adjoint)).clm_comp continuous_id).clm_comp continuous_const

/-- The first high-compression inequality of Lemma 4.4 for every
self-adjoint contraction, including spectra meeting `-1`, `0` or `1`.
The integer in the manuscript is `r=n+2`. -/
theorem high_compression (ι : E →ₗᵢ[ℂ] F) {T : F →L[ℂ] F}
    (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1) (n : ℕ) :
    compression ι (cfc (fun x : ℝ => thermalIncrement
      (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) |x|) T) ≤
      cfc (fun x : ℝ => thermalIncrement
        (((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)) |x|) (compression ι T) := by
  let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hleft := (continuous_compression ι).continuousAt.tendsto.comp
    (tendsto_thermal_cfc_smul hb hT hnorm)
  have hright := tendsto_thermal_cfc_smul hb (compression_isSelfAdjoint ι hT)
    ((norm_compression_le ι T).trans hnorm)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with t ht
  dsimp only [Function.comp_def, b]
  simpa only [compression_real_smul] using high_compression_of_norm_lt_one ι
    ((show IsSelfAdjoint t by cfc_tac).smul hT) (norm_smul_lt_one hnorm ht) n

/-- Lemma 4.3 in signed commutation coordinates: the thermal function is
evaluated at the absolute spectral value while the reserve is `sqrt(1-T²)`.
This reuses the established scalar comparison, including its endpoints. -/
theorem thermal_comparison_signed {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    {T : F →L[ℂ] F} (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1) :
    thermalConst b • (reserve T) ^ (2 * b) ≤
      cfc (fun x : ℝ => thermalIncrement b |x|) T := by
  have hspec : spectrum ℝ T ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun _ hx => spectrum_mem_Icc_of_norm_le_one hnorm hx
  have hsq : ∀ x ∈ spectrum ℝ T, x ^ 2 ≤ 1 := by
    intro x hx
    have h := hspec hx
    nlinarith [h.1, h.2]
  have hR : Continuous (fun x : ℝ => (1 - x ^ 2) ^ b) :=
    (continuous_const.sub (continuous_pow 2)).rpow_const (fun _ => Or.inr hb0.le)
  change thermalConst b • CFC.sqrt (1 - T ^ 2) ^ (2 * b) ≤ _
  rw [sqrt_one_sub_sq_rpow hb0.le (one_sub_sq_nonneg hT hsq),
    one_sub_sq_rpow_eq_cfc hb0.le hT hsq,
    ← cfc_const_mul (thermalConst b) (fun x : ℝ => (1 - x ^ 2) ^ b) T hR.continuousOn]
  apply cfc_mono _ (continuous_const.mul hR).continuousOn
    ((continuousOn_thermalIncrement_abs hb0).mono hspec)
  intro x hx
  change thermalConst b * (1 - x ^ 2) ^ b ≤ thermalIncrement b |x|
  simpa only [sq_abs] using thermalIncrement_ge hb0 hb1
    (show |x| ∈ Set.Icc (0 : ℝ) 1 from ⟨abs_nonneg x, abs_le.mpr (hspec hx)⟩)

/-- Both inequalities in the source's high-compression chain, on actual
self-adjoint contractions and actual thermal/reserve functional calculus.
The remaining physical-model bridge identifies `T` with `i J/2`. -/
theorem high_compression_chain (ι : E →ₗᵢ[ℂ] F) {T : F →L[ℂ] F}
    (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1) (n : ℕ) :
    let b : ℝ := ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ)
    thermalConst b • compression ι ((reserve T) ^ (2 * b)) ≤
        compression ι (cfc (fun x : ℝ => thermalIncrement b |x|) T) ∧
      compression ι (cfc (fun x : ℝ => thermalIncrement b |x|) T) ≤
        cfc (fun x : ℝ => thermalIncrement b |x|) (compression ι T) := by
  dsimp only
  have hb0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) := by positivity
  have hb1 : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact_mod_cast (show n + 1 < n + 2 by omega)
  refine ⟨?_, high_compression ι hT hnorm n⟩
  simpa only [compression_real_smul] using
    compression_mono ι (thermal_comparison_signed hb0 hb1 hT hnorm)

end VacuumBellSeparation.Gaussian
