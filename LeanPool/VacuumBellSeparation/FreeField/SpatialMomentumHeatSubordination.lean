/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatFourierFubini
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroInner
public import LeanPool.VacuumBellSeparation.FreeField.Lorentz

/-!
# Actual heat subordination of the momentum covariance pairing

Multiplication by the squared dispersion preserves integrability for the
original compact spatial tests, by their proved Schwartz decay. The
reciprocal-energy Fubini theorem therefore applies to this actual weighted
pairing, with no interchange assumed as a hypothesis.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ComplexConjugate

theorem integrable_dispersion_sq_spatialFourier_product (m : ℝ)
    (f g : SpatialTestFunction) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ((dispersion m p) ^ 2 : ℝ) *
        (conj (spatialFourier f p) * spatialFourier g p)) := by
  have h0 := (integrable_spatialFourier_product f g).norm.const_mul (m ^ 2)
  have h2 := integrable_pow_norm_spatialFourier_product f g 2
  refine (h0.add h2).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp ((continuous_dispersion m).pow 2)).mul
      ((continuous_spatialFourier f).star.mul (continuous_spatialFourier g))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun p => ?_)
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      dispersion_sq, Pi.add_apply]
    rw [abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact le_of_eq (by ring)

theorem integrable_momentumEnergyHeatPairing {m : ℝ} (hm : 0 < m)
    (f g : SpatialTestFunction) :
    Integrable (reciprocalEnergyHeatPairing m (fun p =>
      ((dispersion m p) ^ 2 : ℝ) *
        (conj (spatialFourier f p) * spatialFourier g p)))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) :=
  integrable_reciprocalEnergyHeatPairing hm
    ((Complex.continuous_ofReal.comp ((continuous_dispersion m).pow 2)).mul
      ((continuous_spatialFourier f).star.mul (continuous_spatialFourier g)))
    (integrable_dispersion_sq_spatialFourier_product m f g)

theorem spatialFourier_momentum_energy_heat {m : ℝ} (hm : 0 < m)
    (f g : SpatialTestFunction) :
    (∫ p : EuclideanSpace ℝ (Fin 3), (dispersion m p : ℂ) *
      (conj (spatialFourier f p) * spatialFourier g p)) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
            ∫ p : EuclideanSpace ℝ (Fin 3), (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
              (((m ^ 2 + ‖p‖ ^ 2 : ℝ) : ℂ) *
                (conj (spatialFourier f p) * spatialFourier g p)) := by
  have h := reciprocal_dispersion_integral_heat_separated hm
    ((Complex.continuous_ofReal.comp ((continuous_dispersion m).pow 2)).mul
      ((continuous_spatialFourier f).star.mul (continuous_spatialFourier g)))
    (integrable_dispersion_sq_spatialFourier_product m f g)
  have hleft : (fun p : EuclideanSpace ℝ (Fin 3) =>
      (((dispersion m p)⁻¹ : ℝ) : ℂ) *
        (((dispersion m p) ^ 2 : ℝ) *
          (conj (spatialFourier f p) * spatialFourier g p))) =
      fun p => (dispersion m p : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p) := by
    funext p
    have hp : (dispersion m p : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (dispersion_pos hm.ne' p).ne'
    push_cast
    field_simp
  simp only [Function.comp_apply, Pi.mul_apply, Pi.pow_apply, Pi.star_apply,
    starRingEnd_apply] at h hleft
  rw [hleft] at h
  simpa only [dispersion_sq, starRingEnd_apply] using h

end VacuumBellSeparation
