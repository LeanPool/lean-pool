/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatIntegrationByParts

/-!
# The actual negative heat representation of the momentum pairing

The squared-dispersion Fourier integral is the mass term minus the
proved time derivative. All time integration-by-parts conditions have
been discharged, including the separated-support boundary at zero.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ComplexConjugate

theorem integrable_spatialHeatFourier_derivative {t : ℝ} (ht : 0 ≤ t)
    (f g : SpatialTestFunction) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => (-(‖p‖ ^ 2 : ℝ) : ℂ) *
      ((Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p))) := by
  apply (integrable_pow_norm_spatialFourier_product f g 2).mono'
  · exact (show Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
      (-(‖p‖ ^ 2 : ℝ) : ℂ) * ((Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p))) by
      have hf := continuous_spatialFourier f
      have hg := continuous_spatialFourier g
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (spatialHeatFourier_derivative_integrand_bound ht f g)

theorem spatialHeat_squared_energy_eq_mass_sub_derivative (m : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (f g : SpatialTestFunction) :
    (∫ p : EuclideanSpace ℝ (Fin 3), (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
      (((m ^ 2 + ‖p‖ ^ 2 : ℝ) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p))) =
      ((m ^ 2 : ℝ) : ℂ) * spatialHeatFourierPairing f g t -
        spatialHeatFourierDerivative f g t := by
  unfold spatialHeatFourierPairing spatialHeatFourierDerivative
  rw [← integral_const_mul, ← integral_sub
    ((integrable_spatialHeatFourier_pairing ht f g).const_mul ((m ^ 2 : ℝ) : ℂ))
    (integrable_spatialHeatFourier_derivative ht f g)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun p => ?_)
  push_cast
  ring

theorem spatialFourier_momentum_negative_heat {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    (∫ p : EuclideanSpace ℝ (Fin 3), (dispersion m p : ℂ) *
      (conj (spatialFourier f p) * spatialFourier g p)) =
      ((-1 / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          ((t ^ (-(3 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
            spatialHeatFourierPairing f g t := by
  rw [spatialFourier_momentum_energy_heat hm f g]
  have heq := setIntegral_congr_fun (μ := volume) measurableSet_Ioi (fun t (ht : t ∈ Ioi (0 : ℝ)) =>
    congrArg (fun z : ℂ => spatialHeatMassWeight m t * z)
      (spatialHeat_squared_energy_eq_mass_sub_derivative m ht.le f g))
  change ((Real.sqrt Real.pi)⁻¹ : ℂ) *
    (∫ t in Ioi (0 : ℝ), spatialHeatMassWeight m t * _) = _
  rw [heq, spatialHeat_time_integration_by_parts hm hd f g hsep]
  push_cast
  ring

end VacuumBellSeparation
