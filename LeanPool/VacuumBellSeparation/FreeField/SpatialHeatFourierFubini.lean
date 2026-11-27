/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatSubordination
public import LeanPool.VacuumBellSeparation.FreeField.SpatialFourier

/-!
# Genuine heat-parameter Fubini for the reciprocal-energy Fourier pairing

A product of the integrable mass-only Gamma weight and the absolute
Fourier pairing dominates the actual joint integrand. This discharges
the first interchange in the heat-kernel covariance proof.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory Set
open scoped ComplexConjugate

/-- Reciprocal energy heat pairing given by `((tp.1 ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2 + ‖tp.2‖ ^
2) * tp.1) : ℝ) : ℂ) * g tp.2`. -/
noncomputable def reciprocalEnergyHeatPairing (m : ℝ)
    (g : EuclideanSpace ℝ (Fin 3) → ℂ) (tp : ℝ × EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ((tp.1 ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2 + ‖tp.2‖ ^ 2) * tp.1) : ℝ) : ℂ) * g tp.2

theorem integrable_reciprocalEnergyHeatPairing {m : ℝ} (hm : 0 < m)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hgc : Continuous g) (hgi : Integrable g) :
    Integrable (reciprocalEnergyHeatPairing m g)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have ht : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t))
      (Ioi 0) := integrableOn_laplace_rpow (by positivity) (by norm_num)
  have hmajor := ht.mul_prod hgi.norm
  apply hmajor.mono'
  · exact (show Measurable (reciprocalEnergyHeatPairing m g) by
      unfold reciprocalEnergyHeatPairing
      have hg := hgc.measurable
      fun_prop).aestronglyMeasurable
  · have htpos : ∀ᵐ tp : ℝ × EuclideanSpace ℝ (Fin 3)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod volume), 0 < tp.1 := by
      apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact Filter.Eventually.of_forall (fun _ => ht)
    filter_upwards [htpos] with tp htp
    have htexp : Real.exp (-(m ^ 2 + ‖tp.2‖ ^ 2) * tp.1) ≤ Real.exp (-(m ^ 2) * tp.1) := by
      apply Real.exp_le_exp.mpr
      have hsq := mul_nonneg (sq_nonneg ‖tp.2‖) htp.le
      nlinarith
    simp only [reciprocalEnergyHeatPairing, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg htp.le _), abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htexp (Real.rpow_nonneg htp.le _)) (norm_nonneg _)

theorem reciprocal_dispersion_integral_heat {m : ℝ} (hm : 0 < m)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hgc : Continuous g) (hgi : Integrable g) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion m p)⁻¹ : ℝ) * g p) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) *
        ∫ t in Ioi (0 : ℝ), ∫ p : EuclideanSpace ℝ (Fin 3),
          reciprocalEnergyHeatPairing m g (t, p) := by
  have hj := integrable_reciprocalEnergyHeatPairing hm hgc hgi
  calc
    _ = ((Real.sqrt Real.pi)⁻¹ : ℂ) *
        ∫ p : EuclideanSpace ℝ (Fin 3), ∫ t in Ioi (0 : ℝ),
          reciprocalEnergyHeatPairing m g (t, p) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun p => ?_)
      simp only [reciprocalEnergyHeatPairing]
      rw [integral_mul_const, integral_complex_ofReal, reciprocal_dispersion_heat hm]
      push_cast
      ring
    _ = _ := by
      congr 1
      exact (integral_integral_swap (f := fun t p => reciprocalEnergyHeatPairing m g (t,
        p)) hj).symm

theorem reciprocal_dispersion_integral_heat_separated {m : ℝ} (hm : 0 < m)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hgc : Continuous g) (hgi : Integrable g) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion m p)⁻¹ : ℝ) * g p) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
            ∫ p : EuclideanSpace ℝ (Fin 3), (Real.exp (-t * ‖p‖ ^ 2) : ℂ) * g p := by
  rw [reciprocal_dispersion_integral_heat hm hgc hgi]
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun t => ?_)
  dsimp only
  rw [← integral_const_mul]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun p => ?_)
  simp only [reciprocalEnergyHeatPairing]
  rw [show -(m ^ 2 + ‖p‖ ^ 2) * t = -(m ^ 2) * t + -t * ‖p‖ ^ 2 by ring, Real.exp_add]
  push_cast
  ring

theorem spatialFourier_reciprocal_energy_heat {m : ℝ} (hm : 0 < m)
    (f g : SpatialTestFunction) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion m p)⁻¹ : ℝ) *
      (conj (spatialFourier f p) * spatialFourier g p)) =
      ((Real.sqrt Real.pi)⁻¹ : ℂ) *
        ∫ t in Ioi (0 : ℝ),
          ((t ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) * t) : ℝ) : ℂ) *
            ∫ p : EuclideanSpace ℝ (Fin 3), (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
              (conj (spatialFourier f p) * spatialFourier g p) :=
  reciprocal_dispersion_integral_heat_separated hm
    ((continuous_spatialFourier f).star.mul (continuous_spatialFourier g))
    (integrable_spatialFourier_product f g)

end VacuumBellSeparation
