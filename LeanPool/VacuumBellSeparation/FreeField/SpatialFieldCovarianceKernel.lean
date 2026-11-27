/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialFieldCovarianceKernelDefs
public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatSeparatedIntegrability

/-!
# The actual separated field covariance kernel

Both required Fubini exchanges have proved joint integrability. The
literal reciprocal-energy Fourier pairing therefore equals the actual
Bessel kernel pairing of the original real spatial tests.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory Set
open scoped ComplexConjugate

theorem spatialHeat_scalar_normalization (A B : ℂ) :
    (((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) * ((Real.sqrt Real.pi)⁻¹ : ℂ)) * (A * B) =
      ((1 / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) * A * ((((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ * B) := by
  push_cast
  field_simp


theorem integrable_spatialFieldKernel_pairing {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    Integrable (fun xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      (spatialFieldBesselKernel m (xy.1 - xy.2) : ℂ) * (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ))
      (volume.prod volume) := by
  have h := (integrable_separatedHeatPairing hm hd f g hsep).integral_prod_right
  simpa only [integral_separatedHeatPairing_time hm hd f g hsep, spatialFieldBesselKernel] using h

theorem spatialFourier_field_covariance_kernel {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    ((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) *
      (∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion m p)⁻¹ : ℝ) *
        (conj (spatialFourier f p) * spatialFourier g p)) =
      ∫ xy, (spatialFieldBesselKernel m (xy.1 - xy.2) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume := by
  have hj := integrable_separatedHeatPairing hm hd f g hsep
  rw [spatialFourier_reciprocal_energy_heat hm f g, ← mul_assoc, ← integral_const_mul]
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ xy, separatedHeatPairing m f g (t, xy) ∂volume.prod volume := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [spatialHeat_scalar_normalization, spatialFourier_heat_convolution ht f g,
        ← integral_const_mul]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall (fun xy => ?_)
      simp only [separatedHeatPairing, Complex.ofReal_mul]
      ring
    _ = ∫ xy, (∫ t in Ioi (0 : ℝ), separatedHeatPairing m f g (t, xy)) ∂volume.prod volume :=
      integral_integral_swap (f := fun t xy => separatedHeatPairing m f g (t, xy)) hj
    _ = _ := by simp_rw [integral_separatedHeatPairing_time hm hd f g hsep,
      spatialFieldBesselKernel]

theorem spatialFourier_field_covariance_real_kernel {m d : ℝ} (hm : 0 < m) (hd : 0 < d)
    (f g : SpatialTestFunction)
    (hsep : ∀ x y, f.1 x ≠ 0 → g.1 y ≠ 0 → d ≤ ‖x - y‖) :
    (((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) *
      (∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion m p)⁻¹ : ℝ) *
        (conj (spatialFourier f p) * spatialFourier g p))).re =
      ∫ xy, spatialFieldBesselKernel m (xy.1 - xy.2) * f.1 xy.1 * g.1 xy.2 ∂volume.prod volume := by
  rw [spatialFourier_field_covariance_kernel hm hd f g hsep, ← RCLike.re_eq_complex_re,
    ← integral_re (integrable_spatialFieldKernel_pairing hm hd f g hsep)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun xy => by
    simp only [RCLike.re_eq_complex_re, ← Complex.ofReal_mul, Complex.ofReal_re])

end VacuumBellSeparation
