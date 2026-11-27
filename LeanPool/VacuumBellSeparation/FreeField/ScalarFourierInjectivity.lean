/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ScalarSpatialFourier
public import LeanPool.VacuumBellSeparation.FreeField.MassShellDistribution

/-!
# Injectivity of the actual scalar Fourier integral on physical L² ∩ L¹

The normalized Schwartz Fourier pairing is recovered with scale 2π. Its
actual tempered Fourier inverse and the injective physical distribution
embedding prove injectivity. No reciprocal growing multiplier is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter FourierTransform
open scoped FourierTransform InnerProductSpace

theorem schwartzFourier_eq_scaled_spatialIntegral
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 φ) p = ∫ x, Complex.exp (-(Complex.I *
      (((2 * Real.pi) * ⟪p, x⟫_ℝ : ℝ) : ℂ))) * φ x := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 2
    rw [real_inner_comm x p]
    push_cast
    ring

theorem physical_L2_eq_zero_of_scalarSpatialFourier_eq_zero {m : ℝ} (hm : 0 < m)
    (u : Lp ℂ 2 (oneParticleMeasure m))
    (hu : Integrable (fun p => u p) (oneParticleMeasure m))
    (hzero : scalarSpatialFourier (oneParticleMeasure m) (fun p => u p) = 0) : u = 0 := by
  let := oneParticleMeasure_isLocallyFinite hm
  have hFT : 𝓕 (physicalMomentumDistribution hm u) = 0 := by
    ext φ
    rw [TemperedDistribution.fourier_apply, physicalMomentumDistribution_apply]
    have h := integral_scalarSpatialFourier_pairing hu φ.integrable (2 * Real.pi)
    simp only [hzero, Pi.zero_apply, mul_zero, integral_zero,
      ← schwartzFourier_eq_scaled_spatialIntegral] at h
    exact h.symm
  have hd : physicalMomentumDistribution hm u = 0 := by
    calc
      _ = 𝓕⁻ (𝓕 (physicalMomentumDistribution hm u)) := (fourierInv_fourier_eq _).symm
      _ = 0 := by rw [hFT, fourierInv_zero]
  apply physicalMomentumDistribution_injective hm
  simpa only [map_zero] using hd

end VacuumBellSeparation
