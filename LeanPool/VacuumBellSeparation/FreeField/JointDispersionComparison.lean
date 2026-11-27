/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointLowFrequency

/-! # The literal mass comparison for the field component of the joint source -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation
open MeasureTheory

/-- ω_μ ≤ max(1,μ) ω_1, with the original spatial dispersion. -/
theorem dispersion_le_max_one_mass {μ : ℝ} (hμ : 0 ≤ μ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    dispersion μ p ≤ max 1 μ * dispersion 1 p := by
  have hm : μ ≤ max 1 μ := le_max_right _ _
  have h1 : (1 : ℝ) ≤ max 1 μ := le_max_left _ _
  have hsμ := dispersion_sq μ p
  have hs1 := dispersion_sq 1 p
  have hsqμ := pow_le_pow_left₀ hμ hm 2
  have hsq1 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h1 2
  have hp := mul_le_mul_of_nonneg_right hsq1 (sq_nonneg ‖p‖)
  have hdμ : 0 ≤ dispersion μ p := Real.sqrt_nonneg _
  have hd1 : 0 ≤ dispersion 1 p := Real.sqrt_nonneg _
  apply (sq_le_sq₀ hdμ (mul_nonneg (by linarith : 0 ≤ max 1 μ) hd1)).mp
  rw [mul_pow, dispersion_sq, dispersion_sq]
  nlinarith

/-- The inverse multiplier comparison needed for the field Sobolev norm. -/
theorem inv_dispersion_one_le {μ : ℝ} (hμ : 0 < μ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (dispersion 1 p)⁻¹ ≤ max 1 μ * (dispersion μ p)⁻¹ := by
  have hdμ : 0 < dispersion μ p := dispersion_pos hμ.ne' p
  have hd1 : 0 < dispersion 1 p := dispersion_pos (by norm_num) p
  have hm : 0 < max 1 μ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h := dispersion_le_max_one_mass hμ.le p
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ hdμ).mpr
  have hi := (div_le_iff₀ hd1).mpr h
  simpa only [div_eq_mul_inv, mul_comm] using hi

theorem integrable_inv_dispersion_fourier_norm_sq {μ : ℝ} (hμ : 0 < μ)
    (f : SpatialTestFunction) :
    Integrable (fun p => (dispersion μ p)⁻¹ * ‖spatialFourier f p‖ ^ 2) := by
  have h := (integrable_inv_dispersion_spatialFourier_product hμ f f).norm
  convert h using 1
  funext p
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ dispersion μ p from Real.sqrt_nonneg _))]
  ring

/-- Squared version of source equation (7.2), preserving all Fourier factors. -/
theorem joint_field_mass_comparison {μ : ℝ} (hμ : 0 < μ) (f : SpatialTestFunction) :
    (∫ p, (dispersion 1 p)⁻¹ * ‖spatialFourier f p‖ ^ 2) ≤
      max 1 μ * ∫ p, (dispersion μ p)⁻¹ * ‖spatialFourier f p‖ ^ 2 := by
  rw [← integral_const_mul]
  apply integral_mono_ae
    (integrable_inv_dispersion_fourier_norm_sq (by norm_num : (0 : ℝ) < 1) f)
    ((integrable_inv_dispersion_fourier_norm_sq hμ f).const_mul _)
  exact Filter.Eventually.of_forall fun p => by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
      (inv_dispersion_one_le hμ p) (sq_nonneg ‖spatialFourier f p‖)

end VacuumBellSeparation
