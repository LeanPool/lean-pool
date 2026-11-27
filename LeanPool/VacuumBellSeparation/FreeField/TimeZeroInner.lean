/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialFourier

/-!
# Integrability of time-zero mass-shell pairings

The smooth compactly supported sources are evaluated in the manuscript's
mass-shell measure, with no integrability supplied as a model assumption.
The weighted Fourier pairings below are the ingredients of the Gram identity.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

theorem dispersion_le_mass_add_norm {m : ℝ} (hm : 0 ≤ m)
    (p : EuclideanSpace ℝ (Fin 3)) : dispersion m p ≤ m + ‖p‖ := by
  have hs := Real.sq_sqrt (show 0 ≤ m ^ 2 + ‖p‖ ^ 2 by positivity)
  have hp := Real.sqrt_nonneg (m ^ 2 + ‖p‖ ^ 2)
  have hn := norm_nonneg p
  unfold dispersion
  nlinarith [mul_nonneg hm hn]

theorem integrable_inv_dispersion_spatialFourier_product {m : ℝ} (hm : 0 < m)
    (f g : SpatialTestFunction) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (conj (spatialFourier f p) * spatialFourier g p) * ((dispersion m p)⁻¹ : ℝ)) := by
  refine (integrable_spatialFourier_product f g).mul_bdd (c := m⁻¹)
    (Complex.continuous_ofReal.comp ((continuous_dispersion m).inv₀
      (fun p => (hm.trans_le (le_dispersion hm.le p)).ne'))).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun p => ?_
  have hd : 0 < dispersion m p := hm.trans_le (le_dispersion hm.le p)
  change ‖(((dispersion m p)⁻¹ : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  exact inv_anti₀ hm (le_dispersion hm.le p)

theorem integrable_dispersion_spatialFourier_product {m : ℝ} (hm : 0 ≤ m)
    (f g : SpatialTestFunction) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (conj (spatialFourier f p) * spatialFourier g p) * (dispersion m p : ℂ)) := by
  have h0 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖spatialFourier f p‖ * ‖spatialFourier g p‖) := by
    simpa only [pow_zero, one_mul] using integrable_pow_norm_spatialFourier_product f g 0
  have h1 : Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (‖p‖ * ‖spatialFourier f p‖) * ‖spatialFourier g p‖) := by
    simpa only [pow_one] using integrable_pow_norm_spatialFourier_product f g 1
  refine ((h0.const_mul m).add h1).mono' ?_ ?_
  · exact (((Complex.continuous_conj.comp (continuous_spatialFourier f)).mul
      (continuous_spatialFourier g)).mul
        (Complex.continuous_ofReal.comp (continuous_dispersion m))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ dispersion m p from Real.sqrt_nonneg _)]
    have h := mul_le_mul_of_nonneg_left (dispersion_le_mass_add_norm hm p)
      (mul_nonneg (norm_nonneg (spatialFourier f p)) (norm_nonneg (spatialFourier g p)))
    change _ ≤ m * (‖spatialFourier f p‖ * ‖spatialFourier g p‖) +
      ‖p‖ * ‖spatialFourier f p‖ * ‖spatialFourier g p‖
    nlinarith

/-- Pointwise expansion separating the two diagonal terms and symplectic cross term. -/
theorem timeZeroOneParticle_product_expand {m : ℝ} (hm : 0 < m)
    (u v : TimeZeroSource) (p : EuclideanSpace ℝ (Fin 3)) :
    conj (timeZeroOneParticle m u p) * timeZeroOneParticle m v p *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ) =
      ((conj (spatialFourier u.1 p) * spatialFourier v.1 p) * ((dispersion m p)⁻¹ : ℝ) +
        (conj (spatialFourier u.2 p) * spatialFourier v.2 p) * (dispersion m p : ℂ) +
        Complex.I * (conj (spatialFourier u.1 p) * spatialFourier v.2 p -
          conj (spatialFourier u.2 p) * spatialFourier v.1 p)) *
        ((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) := by
  have hd : (dispersion m p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hm.trans_le (le_dispersion hm.le p)).ne'
  have hc : (2 * (2 * (Real.pi : ℂ)) ^ 3) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (pow_ne_zero 3
      (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hnum : conj (timeZeroOneParticle m u p) * timeZeroOneParticle m v p =
      conj (spatialFourier u.1 p) * spatialFourier v.1 p +
        (dispersion m p : ℂ) ^ 2 * conj (spatialFourier u.2 p) * spatialFourier v.2 p +
        Complex.I * (dispersion m p : ℂ) *
          (conj (spatialFourier u.1 p) * spatialFourier v.2 p -
            conj (spatialFourier u.2 p) * spatialFourier v.1 p) := by
    simp only [timeZeroOneParticle, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    linear_combination (-(dispersion m p : ℂ) ^ 2 *
      conj (spatialFourier u.2 p) * spatialFourier v.2 p) * Complex.I_sq
  rw [hnum]
  push_cast
  field_simp [hd, hc]

/-- Integrability is derived from Schwartz decay, including the energy-weighted term. -/
theorem integrable_timeZeroOneParticleInner_integrand {m : ℝ} (hm : 0 < m)
    (u v : TimeZeroSource) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      conj (timeZeroOneParticle m u p) * timeZeroOneParticle m v p *
        ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)) := by
  simp_rw [timeZeroOneParticle_product_expand hm]
  exact (((integrable_inv_dispersion_spatialFourier_product hm u.1 v.1).add
    (integrable_dispersion_spatialFourier_product hm.le u.2 v.2)).add
      (((integrable_spatialFourier_product u.1 v.2).sub
        (integrable_spatialFourier_product u.2 v.1)).const_mul Complex.I)).mul_const _

end VacuumBellSeparation
