/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroL2

/-!
# Physical mass-shell L² bound for actual spatial Fourier transforms

The bound uses the literal density `1 / (2(2π)^3 ω)` and Parseval in
the manuscript's Fourier convention. Actual integrability is proved
separately, so no default value of a nonintegrable integral is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped ComplexConjugate

theorem integrable_spatialFourier_norm_sq (f : SpatialTestFunction) :
    Integrable (fun p => ‖spatialFourier f p‖ ^ 2) := by
  simpa only [spatialFourierSchwartz_apply] using
    ((spatialFourierSchwartz f).memLp 2).norm.integrable_sq

theorem integral_spatialFourier_norm_sq (f : SpatialTestFunction) :
    (∫ p, ‖spatialFourier f p‖ ^ 2) =
      (2 * Real.pi) ^ 3 * ∫ x, (f.1 x) ^ 2 := by
  apply Complex.ofReal_injective
  calc
    ((∫ p, ‖spatialFourier f p‖ ^ 2 : ℝ) : ℂ) =
        ∫ p, ((‖spatialFourier f p‖ ^ 2 : ℝ) : ℂ) := integral_ofReal.symm
    _ = ∫ p, conj (spatialFourier f p) * spatialFourier f p := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        change ((‖spatialFourier f p‖ ^ 2 : ℝ) : ℂ) =
          conj (spatialFourier f p) * spatialFourier f p
        rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
        ∫ x, (f.1 x : ℂ) * (f.1 x : ℂ) := integral_spatialFourier_product f f
    _ = (((2 * Real.pi) ^ 3 * ∫ x, (f.1 x) ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_mul]
      congr 1
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by push_cast; ring

theorem memLp_spatialFourier_massShell {m : ℝ} (hm : 0 < m)
    (f : SpatialTestFunction) : MemLp (spatialFourier f) 2 (oneParticleMeasure m) := by
  have h : timeZeroOneParticle m (f, 0) = spatialFourier f := by
    funext p
    have hz : spatialFourier (0 : SpatialTestFunction) p = 0 := by
      change (∫ x, Complex.exp (-(Complex.I * ↑(inner ℝ p x))) * (0 : ℂ)) = 0
      simp
    simp only [timeZeroOneParticle, hz, mul_zero, add_zero]
  simpa only [h] using memLp_timeZeroOneParticle hm (f, 0)

theorem integrable_spatialFourier_norm_sq_massShell {m : ℝ} (hm : 0 < m)
    (f : SpatialTestFunction) :
    Integrable (fun p => ‖spatialFourier f p‖ ^ 2) (oneParticleMeasure m) :=
  (memLp_spatialFourier_massShell hm f).norm.integrable_sq

theorem oneParticleWeight_le_mass {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (oneParticleWeight m p : ℝ) ≤ 1 / (2 * (2 * Real.pi) ^ 3 * m) := by
  rw [oneParticleWeight_coe hm]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul_of_nonneg_left (le_dispersion hm.le p) (by positivity)

/-- Exact physical normalization: the Fourier L² norm on the mass shell is
at most `(2m)⁻¹` times the spatial real L² norm squared. -/
theorem integral_spatialFourier_norm_sq_massShell_le {m : ℝ} (hm : 0 < m)
    (f : SpatialTestFunction) :
    (∫ p, ‖spatialFourier f p‖ ^ 2 ∂oneParticleMeasure m) ≤
      (1 / (2 * m)) * ∫ x, (f.1 x) ^ 2 := by
  rw [oneParticleMeasure,
    integral_withDensity_eq_integral_smul (measurable_oneParticleWeight hm)]
  have h : (∫ p, oneParticleWeight m p • ‖spatialFourier f p‖ ^ 2) ≤
      ∫ p, (1 / (2 * (2 * Real.pi) ^ 3 * m)) * ‖spatialFourier f p‖ ^ 2 := by
    apply integral_mono_of_nonneg
    · exact Eventually.of_forall fun p => by positivity
    · exact (integrable_spatialFourier_norm_sq f).const_mul _
    · exact Eventually.of_forall fun p =>
        mul_le_mul_of_nonneg_right (oneParticleWeight_le_mass hm p) (sq_nonneg _)
  refine h.trans_eq ?_
  rw [integral_const_mul, integral_spatialFourier_norm_sq]
  have hm0 : m ≠ 0 := hm.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end VacuumBellSeparation
