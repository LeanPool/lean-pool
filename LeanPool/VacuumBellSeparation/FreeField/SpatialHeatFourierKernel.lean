/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatSubordination
public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselHeatParameter

/-!
# The actual scalar Fourier transform of the spatial heat multiplier

This uses the source phase exp(i p.w), and its exact (2π)^(-3)
normalization. The heat/Bessel scalar identity is compatible with the
reciprocal-energy Gamma factor. Exchanges with source tests are proved in other modules
(`spatialFourier_heat_convolution` in `FreeField/SpatialHeatConvolution.lean`; for tests with
separated supports, `spatialFourier_field_covariance_kernel` in
`FreeField/SpatialFieldCovarianceKernel.lean`).
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory Set
open scoped InnerProductSpace

theorem integrable_spatialHeatFourierIntegrand {t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(t : ℂ) * (‖p‖ : ℂ) ^ 2 + Complex.I * (inner ℝ w p : ℂ))) :=
  GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show 0 < (t : ℂ).re from ht) Complex.I w

theorem integral_spatialHeatFourierIntegrand {t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin 3)) :
    (∫ p : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(t : ℂ) * (‖p‖ : ℂ) ^ 2 + Complex.I * (inner ℝ w p : ℂ))) =
      (((Real.pi / t) ^ (3 / 2 : ℝ) * Real.exp (-‖w‖ ^ 2 / (4 * t)) : ℝ) : ℂ) := by
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (show 0 < (t : ℂ).re from ht) Complex.I w]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat, Complex.I_sq, neg_one_mul]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity)]
  push_cast
  rfl

/-- Three-dimensional Gaussian heat kernel in the Fourier normalization used for the source
covariance. -/
noncomputable def spatialHeatKernel (t : ℝ) (w : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (Real.pi / t) ^ (3 / 2 : ℝ) / (2 * Real.pi) ^ 3 * Real.exp (-‖w‖ ^ 2 / (4 * t))

theorem spatialHeatKernel_fourier {t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin 3)) :
    (spatialHeatKernel t w : ℂ) = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ *
      ∫ p : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(t : ℂ) * (‖p‖ : ℂ) ^ 2 + Complex.I * (inner ℝ w p : ℂ)) := by
  rw [integral_spatialHeatFourierIntegrand ht]
  simp only [spatialHeatKernel, Complex.ofReal_mul, Complex.ofReal_div]
  ring

theorem spatialHeatKernel_nonneg {t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin 3)) : 0 ≤ spatialHeatKernel t w := by
  unfold spatialHeatKernel
  positivity

theorem heat_subordination_prefactor {t : ℝ} (ht : 0 < t) :
    (1 / (2 * Real.sqrt Real.pi)) * t ^ (-(1 / 2 : ℝ)) *
        ((Real.pi / t) ^ (3 / 2 : ℝ) / (2 * Real.pi) ^ 3) =
      (1 / (16 * Real.pi ^ 2)) * t ^ (-2 : ℤ) := by
  have hpow : (Real.pi / t) ^ (3 / 2 : ℝ) =
      (Real.pi / t) * Real.sqrt (Real.pi / t) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpow, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow,
    Real.sqrt_div Real.pi_pos.le, zpow_neg, zpow_ofNat]
  field_simp [ht.ne', Real.pi_ne_zero, ne_of_gt (Real.sqrt_pos.mpr ht),
    ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)]
  ring_nf
  rw [Real.sq_sqrt ht.le]

theorem spatialHeat_subordination_integrand {μ t : ℝ} (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin 3)) :
    (1 / (2 * Real.sqrt Real.pi)) *
        (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w =
      (1 / (16 * Real.pi ^ 2)) * heatBesselIntegrand 1 μ ‖w‖ t := by
  have hp := heat_subordination_prefactor ht
  unfold spatialHeatKernel heatBesselIntegrand
  change (1 / (2 * Real.sqrt Real.pi)) *
      (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) *
      ((Real.pi / t) ^ (3 / 2 : ℝ) / (2 * Real.pi) ^ 3 * Real.exp (-‖w‖ ^ 2 / (4 * t))) =
    (1 / (16 * Real.pi ^ 2)) *
      (t ^ (-2 : ℤ) * Real.exp (-(μ ^ 2 * t) - ‖w‖ ^ 2 / (4 * t)))
  rw [show -(μ ^ 2 * t) - ‖w‖ ^ 2 / (4 * t) = -(μ ^ 2) * t + -‖w‖ ^ 2 / (4 * t) by ring,
    Real.exp_add]
  calc
    _ = ((1 / (2 * Real.sqrt Real.pi)) * t ^ (-(1 / 2 : ℝ)) *
        ((Real.pi / t) ^ (3 / 2 : ℝ) / (2 * Real.pi) ^ 3)) *
        (Real.exp (-(μ ^ 2) * t) * Real.exp (-‖w‖ ^ 2 / (4 * t))) := by ring
    _ = _ := by rw [hp]; ring

theorem spatialHeat_integral_eq_fieldBessel {μ : ℝ} (hμ : 0 < μ)
    (w : EuclideanSpace ℝ (Fin 3)) (hw : w ≠ 0) :
    (∫ t in Ioi (0 : ℝ), (1 / (2 * Real.sqrt Real.pi)) *
      (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w) =
      μ / (4 * Real.pi ^ 2 * ‖w‖) * besselKReal 1 (μ * ‖w‖) := by
  have heq : (∫ t in Ioi (0 : ℝ), (1 / (2 * Real.sqrt Real.pi)) *
      (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w) =
      ∫ t in Ioi (0 : ℝ), (1 / (16 * Real.pi ^ 2)) * heatBesselIntegrand 1 μ ‖w‖ t :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => spatialHeat_subordination_integrand (μ := μ) ht w)
  rw [heq, integral_const_mul, heatFieldKernel_eq_bessel hμ (norm_pos_iff.mpr hw)]

theorem integrableOn_spatialHeat_subordination {μ : ℝ} (hμ : 0 < μ)
    (w : EuclideanSpace ℝ (Fin 3)) (hw : w ≠ 0) :
    IntegrableOn (fun t : ℝ => (1 / (2 * Real.sqrt Real.pi)) *
      (t ^ (-(1 / 2 : ℝ)) * Real.exp (-(μ ^ 2) * t)) * spatialHeatKernel t w) (Ioi 0) := by
  apply ((integrableOn_heatBesselIntegrand 1 hμ (norm_pos_iff.mpr hw)).const_mul
    (1 / (16 * Real.pi ^ 2))).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact (spatialHeat_subordination_integrand (μ := μ) ht w).symm

end VacuumBellSeparation
