/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDilationDefs
public import LeanPool.VacuumBellSeparation.FreeField.Dilation
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDefs

/-!
# Literal time-zero source dilation

The source pair in (2.5) is `(R² f(R·), R g(R·))`, with smooth compactly
supported real functions on three-dimensional space. This module proves its
symplectic invariance and the scaling of its mass-shell source wave function.
It complements the spacetime dilation already used by the Bell theorem.

The time-slice identification (2.3) and the Gram identity (2.6) between the
position-space symplectic form and the mass-shell integral are proved in other
modules (`localAlgebra_doubleCone_eq_timeZeroLocalAlgebra` in `FreeField/TimeSliceTheorem.lean`,
`timeZeroGram_identity` in `FreeField/TimeZeroGram.lean`); no such identification is assumed here.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

theorem integrable_timeZeroSymplectic (u v : TimeZeroSource) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      u.1.1 x * v.2.1 x - u.2.1 x * v.1.1 x) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (u.1.2.1.continuous.mul v.2.2.1.continuous).sub
      (u.2.2.1.continuous.mul v.1.2.1.continuous)
  · exact u.1.2.2.mul_right.sub u.2.2.2.mul_right

/-- The literal time-zero transformation preserves the symplectic form. -/
theorem timeZeroSymplectic_dilate {R : ℝ} (hR : 0 < R) (u v : TimeZeroSource) :
    timeZeroSymplectic (timeZeroDilate R hR.ne' u) (timeZeroDilate R hR.ne' v) =
      timeZeroSymplectic u v := by
  have hcov : (∫ x : EuclideanSpace ℝ (Fin 3),
      u.1.1 (R • x) * v.2.1 (R • x) - u.2.1 (R • x) * v.1.1 (R • x)) =
      |(R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))⁻¹| • timeZeroSymplectic u v :=
    Measure.integral_comp_smul volume
      (fun x => u.1.1 x * v.2.1 x - u.2.1 x * v.1.1 x) R
  have habs : |(R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))⁻¹| = (R ^ 3)⁻¹ := by
    rw [finrank_momentum]
    exact abs_of_pos (inv_pos.mpr (pow_pos hR 3))
  change (∫ x : EuclideanSpace ℝ (Fin 3),
      R ^ 2 * u.1.1 (R • x) * (R * v.2.1 (R • x)) -
        R * u.2.1 (R • x) * (R ^ 2 * v.1.1 (R • x))) = _
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin 3), R ^ 3 *
        (u.1.1 (R • x) * v.2.1 (R • x) - u.2.1 (R • x) * v.1.1 (R • x)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by ring)
    _ = R ^ 3 * (∫ x : EuclideanSpace ℝ (Fin 3),
        u.1.1 (R • x) * v.2.1 (R • x) - u.2.1 (R • x) * v.1.1 (R • x)) :=
      integral_const_mul _ _
    _ = timeZeroSymplectic u v := by
      rw [hcov, habs, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hR.ne'), one_mul]

theorem integrable_spatialFourier (f : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (f.1 x : ℂ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.inner continuous_id))).neg).mul
      (Complex.continuous_ofReal.comp f.2.1.continuous)
  · exact (f.2.2.comp_left Complex.ofReal_zero).mul_left

/-- Change of variables in the exact Fourier convention of Section 2.1. -/
theorem spatialFourier_scale (R : ℝ) (hR : R ≠ 0) (a : ℝ)
    (f : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    spatialFourier (spatialScale R hR a f) (R • p) =
      ((a * |(R ^ 3)⁻¹| : ℝ) : ℂ) * spatialFourier f p := by
  have hcov : (∫ x : EuclideanSpace ℝ (Fin 3),
      Complex.exp (-(Complex.I * (⟪p, R • x⟫_ℝ : ℂ))) * (f.1 (R • x) : ℂ)) =
      |(R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))⁻¹| • spatialFourier f p :=
    Measure.integral_comp_smul volume
      (fun x => Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (f.1 x : ℂ)) R
  calc
    spatialFourier (spatialScale R hR a f) (R • p) =
        ∫ x : EuclideanSpace ℝ (Fin 3), (a : ℂ) *
          (Complex.exp (-(Complex.I * (⟪p, R • x⟫_ℝ : ℂ))) * (f.1 (R • x) : ℂ)) := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      change Complex.exp (-(Complex.I * (⟪R • p, x⟫_ℝ : ℂ))) * (a * f.1 (R • x) : ℝ) =
        (a : ℂ) * (Complex.exp (-(Complex.I * (⟪p, R • x⟫_ℝ : ℂ))) * (f.1 (R • x) : ℂ))
      rw [real_inner_smul_left, real_inner_smul_right]
      push_cast
      ring
    _ = (a : ℂ) * (∫ x : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(Complex.I * (⟪p, R • x⟫_ℝ : ℂ))) * (f.1 (R • x) : ℂ)) :=
      integral_const_mul _ _
    _ = ((a * |(R ^ 3)⁻¹| : ℝ) : ℂ) * spatialFourier f p := by
      rw [hcov, finrank_momentum, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul]

/-- The time-zero source map has the same mass-shell scaling as the spacetime source map. -/
theorem timeZeroOneParticle_dilate (m : ℝ) {R : ℝ} (hR : 0 < R)
    (u : TimeZeroSource) (p : EuclideanSpace ℝ (Fin 3)) :
    timeZeroOneParticle (m * R) (timeZeroDilate R hR.ne' u) (R • p) =
      ((R⁻¹ : ℝ) : ℂ) * timeZeroOneParticle m u p := by
  have habs : |(R ^ 3)⁻¹| = (R ^ 3)⁻¹ := abs_of_pos (inv_pos.mpr (pow_pos hR 3))
  have h2 : R ^ 2 * (R ^ 3)⁻¹ = R⁻¹ := by field_simp [hR.ne']
  have h1 : R * (R ^ 3)⁻¹ = R⁻¹ * R⁻¹ := by field_simp [hR.ne']
  unfold timeZeroOneParticle timeZeroDilate
  rw [spatialFourier_scale, spatialFourier_scale, dispersion_smul m hR.le p, habs, h2, h1]
  push_cast
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  field_simp [hRc]

end VacuumBellSeparation
