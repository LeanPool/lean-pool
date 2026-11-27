/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.RapidityHilbertTransport
public import Mathlib.Analysis.Fourier.LpSpace

/-!
# The normalized Fourier transform on the actual rapidity Hilbert space

Both Hilbert norms use the same constant multiple of Lebesgue measure.
The pointwise Fourier transform is the pinned normalized Lebesgue Fourier
transform; Plancherel therefore extends it to a unitary on this weighted
Hilbert space without changing its 2π convention.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory SchwartzMap FourierTransform
open scoped FourierTransform ENNReal SchwartzMap

instance rapidityMeasure_hasTemperateGrowth : rapidityMeasure.HasTemperateGrowth := by
  obtain ⟨n, hn⟩ := (inferInstance :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).HasTemperateGrowth).exists_integrable
  exact ⟨⟨n, hn.smul_measure (by simp [rapidityDensity])⟩⟩

instance rapidityMeasure_isFiniteMeasureOnCompacts : IsFiniteMeasureOnCompacts rapidityMeasure :=
  IsFiniteMeasureOnCompacts.smul volume (by simp [rapidityDensity])

theorem norm_fourier_toRapidityL2 (f : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) :
    ‖(𝓕 f).toLp 2 rapidityMeasure‖ = ‖f.toLp 2 rapidityMeasure‖ := by
  rw [SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    SchwartzMap.norm_toLp' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  norm_num [Real.rpow_two, rapidityMeasure, integral_smul_measure,
    SchwartzMap.integral_norm_sq_fourier]

/-- The actual normalized Fourier transform, extended from dense Schwartz vectors. -/
noncomputable def rapidityFourier : RapidityL2 ≃ₗᵢ[ℂ] RapidityL2 :=
  (fourierEquiv ℂ 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)).extendOfIsometry
    (toLpCLM ℂ ℂ 2 rapidityMeasure) (toLpCLM ℂ ℂ 2 rapidityMeasure)
    (denseRange_toLpCLM ENNReal.ofNat_ne_top) (denseRange_toLpCLM ENNReal.ofNat_ne_top)
    norm_fourier_toRapidityL2

theorem rapidityFourier_toLp (f : 𝓢(EuclideanSpace ℝ (Fin 3), ℂ)) :
    rapidityFourier (f.toLp 2 rapidityMeasure) = (𝓕 f).toLp 2 rapidityMeasure :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ f

/-- Full physical mass-shell transport followed by the actual Fourier unitary. -/
noncomputable def oneParticleRapidityFourier {m : ℝ} (hm : 0 < m) :
    Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] RapidityL2 :=
  (rapidityUnitary hm).trans rapidityFourier

end VacuumBellSeparation
