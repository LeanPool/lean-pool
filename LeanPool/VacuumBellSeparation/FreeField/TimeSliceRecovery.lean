/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.OneParticleTimeSlice
public import LeanPool.VacuumBellSeparation.FreeField.TimeSliceOscillator

/-!
# Exact one-particle recovery from the actual time-slice source

With the manuscript's positive time exponential, initial Cauchy data `(f,g)`
produce `ĝ - i h f̂`. The physical time-zero pair is therefore recovered by
using Cauchy data `(-g,f)`, in a separate source-pair construction.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter FourierTransform
open scoped FourierTransform

theorem fourier_massiveSchwartzPower_one_apply (m : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 (massiveSchwartzPower m 1 f)) ξ = (massiveSchwartzSymbol m 1 ξ : ℂ) * (𝓕 f) ξ := by
  rw [← massiveFrequencyEnergy_fourier, massiveFrequencyEnergy_apply]

theorem fourier_timeSliceSchwartzSource (ε m t : ℝ) (f g : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 (timeSliceSchwartzSource ε m t f g)) ξ =
      ((deriv (deriv (timeSliceCutoff ε)) t : ℝ) : ℂ) *
        (massiveEvolutionPhase m t ξ * (𝓕 (cauchyPositiveData m f g)) ξ +
          massiveEvolutionPhase m (-t) ξ * (𝓕 (cauchyNegativeData m f g)) ξ) +
      2 * ((deriv (timeSliceCutoff ε) t : ℝ) : ℂ) * ((massiveSchwartzSymbol m 1 ξ : ℂ) *
        Complex.I) *
        (massiveEvolutionPhase m t ξ * (𝓕 (cauchyPositiveData m f g)) ξ -
          massiveEvolutionPhase m (-t) ξ * (𝓕 (cauchyNegativeData m f g)) ξ) := by
  change (FourierTransform.fourierCLM ℂ SpatialSchwartz
    (timeSliceSchwartzSource ε m t f g)) ξ = _
  simp only [timeSliceSchwartzSource, massiveSchwartzCauchy_eq_phases,
    massiveSchwartzCauchyVelocity, map_add, map_sub, map_smul]
  simp only [add_apply, sub_apply, smul_apply,
    FourierTransform.fourierCLM_apply, smul_eq_mul,
    fourier_massiveSchwartzEvolution, fourier_massiveSchwartzPower_one_apply]
  ring

theorem negativeFrequencyData_recovery {m : ℝ} (hm : 0 < m) (f g : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    -2 * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I) * (𝓕 (cauchyNegativeData m f g)) ξ =
      (𝓕 g) ξ - Complex.I * (massiveSchwartzSymbol m 1 ξ : ℂ) * (𝓕 f) ξ := by
  have hinv : (massiveSchwartzSymbol m 1 ξ : ℂ) * (massiveSchwartzSymbol m (-1) ξ : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← massiveSchwartzSymbol_add hm,
      show (1 : ℝ) + -1 = 0 by norm_num, massiveSchwartzSymbol_zero, Complex.ofReal_one]
  have hp : (𝓕 (massiveSchwartzPower m (-1) g)) ξ =
      (massiveSchwartzSymbol m (-1) ξ : ℂ) * (𝓕 g) ξ := by
    simp only [massiveSchwartzPower, SchwartzMap.fourierMultiplierCLM_apply,
      FourierTransform.fourier_fourierInv_eq,
      SchwartzMap.smulLeftCLM_apply_apply
        (hasTemperateGrowth_complex_massiveSchwartzSymbol m (-1)), smul_eq_mul]
  have hd : (𝓕 (cauchyNegativeData m f g)) ξ =
      (1 / 2 : ℂ) * ((𝓕 f) ξ + Complex.I *
        ((massiveSchwartzSymbol m (-1) ξ : ℂ) * (𝓕 g) ξ)) := by
    change (FourierTransform.fourierCLM ℂ SpatialSchwartz
      ((1 / 2 : ℂ) • (f + Complex.I • massiveSchwartzPower m (-1) g))) ξ = _
    rw [map_smul, map_add, map_smul]
    simp only [smul_apply, add_apply,
      FourierTransform.fourierCLM_apply, smul_eq_mul, hp]
  calc
    _ = -Complex.I * (massiveSchwartzSymbol m 1 ξ : ℂ) * (𝓕 f) ξ -
        (Complex.I * Complex.I) *
          ((massiveSchwartzSymbol m 1 ξ : ℂ) * (massiveSchwartzSymbol m (-1) ξ : ℂ)) *
          (𝓕 g) ξ := by rw [hd]; ring
    _ = (massiveSchwartzSymbol m 1 ξ : ℂ) * (massiveSchwartzSymbol m (-1) ξ : ℂ) * (𝓕 g) ξ -
        Complex.I * (massiveSchwartzSymbol m 1 ξ : ℂ) * (𝓕 f) ξ := by
      rw [Complex.I_mul_I]
      ring
    _ = _ := by rw [hinv, one_mul]

/-- Exact, unconditional one-particle formula for the constructed source,
under the actual support and real-data assumptions needed to construct it. -/
theorem oneParticle_timeSliceTestFunction {m ε r : ℝ}
    (hm : 0 < m) (hε : 0 < ε) (hr : 0 ≤ r) (x₀ : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) (hf : tsupport f ⊆ Metric.closedBall x₀ r)
    (hg : tsupport g ⊆ Metric.closedBall x₀ r)
    (hfr : spatialSchwartzConjugate f = f) (hgr : spatialSchwartzConjugate g = g)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (timeSliceTestFunction hm hε hr x₀ f g hf hg) ((2 * Real.pi) • ξ) =
      (𝓕 g) ξ - Complex.I * (massiveSchwartzSymbol m 1 ξ : ℂ) * (𝓕 f) ξ := by
  rw [oneParticle_timeSliceTestFunction_eq_time_fourier hm hε hr x₀ f g hf hg hfr hgr]
  have heq : (fun t => massiveEvolutionPhase m t ξ * (𝓕 (timeSliceSchwartzSource ε m t f g)) ξ) =
      timeSliceOscillatorReduced ε m ξ (𝓕 (cauchyPositiveData m f g) ξ)
        (𝓕 (cauchyNegativeData m f g) ξ) := by
    funext t
    rw [fourier_timeSliceSchwartzSource]
    exact timeSliceOscillator_reduction ε m ξ _ _ t
  rw [heq, integral_timeSliceOscillatorReduced hε]
  exact negativeFrequencyData_recovery hm f g ξ

end VacuumBellSeparation
