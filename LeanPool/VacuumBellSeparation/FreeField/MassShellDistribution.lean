/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Existence
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Physical one-particle vectors as tempered distributions

The massive shell density is bounded by its value at zero momentum. Consequently
the physical mass-shell measure has temperate growth and is locally finite.
Mathlib's actual `Lp` embedding gives a continuous injective map to tempered
distributions, with the mass-shell density retained in the pairing. Removing
that density, reconstructing the two position-space components, and proving
their compact distributional support are separate steps.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap

namespace VacuumBellSeparation

theorem oneParticleWeight_le {m : ℝ} (hm : 0 < m) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticleWeight m p ≤ Real.toNNReal (1 / (2 * (2 * Real.pi) ^ 3 * m)) := by
  apply Real.toNNReal_mono
  apply one_div_le_one_div_of_le
  · positivity
  · exact mul_le_mul_of_nonneg_left (le_dispersion hm.le p) (by positivity)

/-- The massive shell measure is dominated by a finite constant times spatial volume. -/
theorem oneParticleMeasure_le_volume {m : ℝ} (hm : 0 < m) :
    oneParticleMeasure m ≤
      (Real.toNNReal (1 / (2 * (2 * Real.pi) ^ 3 * m)) : ENNReal) •
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  rw [← withDensity_const]
  apply withDensity_mono
  exact Filter.Eventually.of_forall fun p => by
    change (oneParticleWeight m p : ENNReal) ≤
      (Real.toNNReal (1 / (2 * (2 * Real.pi) ^ 3 * m)) : ENNReal)
    exact ENNReal.coe_le_coe.mpr (oneParticleWeight_le hm p)

/-- Temperate growth is derived from the actual massive measure, not supplied as a model
assumption. -/
theorem oneParticleMeasure_hasTemperateGrowth {m : ℝ} (hm : 0 < m) :
    (oneParticleMeasure m).HasTemperateGrowth := by
  let μ : Measure (EuclideanSpace ℝ (Fin 3)) := volume
  refine ⟨⟨μ.integrablePower, ?_⟩⟩
  have h := (Measure.integrable_pow_neg_integrablePower μ).smul_measure
    (c := (Real.toNNReal (1 / (2 * (2 * Real.pi) ^ 3 * m)) : ENNReal)) (by simp)
  exact h.mono_measure (oneParticleMeasure_le_volume hm)

theorem oneParticleMeasure_isLocallyFinite {m : ℝ} (hm : 0 < m) :
    IsLocallyFiniteMeasure (oneParticleMeasure m) := by
  apply MeasureTheory.IsLocallyFiniteMeasure.withDensity_coe
  exact continuous_real_toNNReal.comp (continuous_oneParticleWeightReal hm)

/-- The actual weighted momentum-distribution embedding. -/
noncomputable def physicalMomentumDistribution {m : ℝ} (hm : 0 < m) :
    Lp ℂ 2 (oneParticleMeasure m) →L[ℂ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ := by
  letI := oneParticleMeasure_hasTemperateGrowth hm
  exact Lp.toTemperedDistributionCLM ℂ (oneParticleMeasure m) 2

theorem physicalMomentumDistribution_apply {m : ℝ} (hm : 0 < m)
    (u : Lp ℂ 2 (oneParticleMeasure m)) (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    physicalMomentumDistribution hm u φ = ∫ p, φ p * u p ∂oneParticleMeasure m := by
  let := oneParticleMeasure_hasTemperateGrowth hm
  exact Lp.toTemperedDistribution_apply u φ

/-- No physical vector is lost in the distribution embedding. -/
theorem physicalMomentumDistribution_injective {m : ℝ} (hm : 0 < m) :
    Function.Injective (physicalMomentumDistribution hm) := by
  let := oneParticleMeasure_hasTemperateGrowth hm
  let := oneParticleMeasure_isLocallyFinite hm
  exact LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := oneParticleMeasure m) (p := 2))

/-- On the existing spacetime source vectors the distribution is the literal mass-shell pairing. -/
theorem physicalMomentumDistribution_oneParticleL2 {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    physicalMomentumDistribution hm (oneParticleL2 hm F) φ =
      ∫ p, φ p * oneParticle m F p ∂oneParticleMeasure m := by
  rw [physicalMomentumDistribution_apply]
  apply integral_congr_ae
  filter_upwards [coeFn_oneParticleL2 hm F] with p hp
  rw [hp]

end VacuumBellSeparation
