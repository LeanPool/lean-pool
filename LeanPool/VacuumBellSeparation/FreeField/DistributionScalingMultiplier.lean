/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceDistributions

/-!
# Normalized Fourier relation for the actual completed source distributions

Coordinate scaling commutes with a genuine temperate multiplier by scaling
its actual symbol. Thus the kernel equation for the physical source becomes
the equation between the Fourier transforms of its position distributions,
with the energy evaluated at `2πξ`.
-/

@[expose] public section

open scoped SchwartzMap FourierTransform

namespace VacuumBellSeparation

theorem hasTemperateGrowth_scale_symbol (c : ℝ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : Function.HasTemperateGrowth g) :
    Function.HasTemperateGrowth (fun p => g (c • p)) :=
  hg.comp (by fun_prop)

theorem spatialDistributionScale_smulLeftCLM
    (c : ℝ) (hc : 0 < c) (g : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hg : Function.HasTemperateGrowth g)
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
    spatialDistributionScale c hc (TemperedDistribution.smulLeftCLM ℂ g T) =
      TemperedDistribution.smulLeftCLM ℂ (fun p => g (c • p))
        (spatialDistributionScale c hc T) := by
  ext φ
  rw [spatialDistributionScale_apply, TemperedDistribution.smulLeftCLM_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, spatialDistributionScale_apply]
  congr 2
  ext p
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_scale_symbol c hg),
    spatialSchwartzScale_apply, smul_inv_smul₀ hc.ne']

theorem fourier_sourceInverseFourier
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
    𝓕 (sourceInverseFourier T) = spatialDistributionScale (2 * Real.pi) (by positivity) T := by
  rw [sourceInverseFourier_apply, FourierTransform.fourier_fourierInv_eq]

/-- The exact normalized-frequency multiplier, with no hidden change of mass. -/
noncomputable def normalizedSourceSecondMultiplier (m : ℝ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  sourceSecondInverseMultiplier m ((2 * Real.pi) • p)

theorem hasTemperateGrowth_normalizedSourceSecondMultiplier {m : ℝ} (hm : 0 < m) :
    Function.HasTemperateGrowth (normalizedSourceSecondMultiplier m) :=
  hasTemperateGrowth_scale_symbol (2 * Real.pi)
    (hasTemperateGrowth_sourceSecondInverseMultiplier hm)

theorem complexSource_fourier_distribution_relation_of_kernel
    {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))
    (z : ComplexSourceHilbert hm U) (hz : complexSourceMap hm U z = 0) :
    𝓕 (complexSourceFirstDistribution hm U z) +
      TemperedDistribution.smulLeftCLM ℂ (normalizedSourceSecondMultiplier m)
        (𝓕 (complexSourceSecondDistribution hm U z)) = 0 := by
  have h := congrArg (spatialDistributionScale (2 * Real.pi) (by positivity))
    (complexSource_distribution_relation_of_kernel hm U z hz)
  rw [map_add, map_zero, spatialDistributionScale_smulLeftCLM _ _ _
    (hasTemperateGrowth_sourceSecondInverseMultiplier hm)] at h
  rw [complexSourceFirstDistribution_fourier, complexSourceSecondDistribution_fourier,
    fourier_sourceInverseFourier, fourier_sourceInverseFourier]
  exact h

end VacuumBellSeparation
