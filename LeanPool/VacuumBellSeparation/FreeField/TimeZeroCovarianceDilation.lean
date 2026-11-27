/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroGram

/-!
# Time-zero covariance dilation in Fourier variables

This completes the literal source-pair scaling calculation for the Fourier
covariance. The library states the covariance (2.2) in Fourier variables, with the multiplier
`(μ² + |𝐩|²)^{1/2}` in place of the position-space operator `h_μ = (-∇² + μ²)^{1/2}`; the
time-slice identification (2.3) is proved in `FreeField/TimeSliceTheorem.lean`
(`localAlgebra_doubleCone_eq_timeZeroLocalAlgebra`).
-/

@[expose] public section

open scoped ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

theorem timeZeroOneParticleInner_dilate (m : ℝ) {R : ℝ} (hR : 0 < R)
    (u v : TimeZeroSource) :
    timeZeroOneParticleInner (m * R) (timeZeroDilate R hR.ne' u)
      (timeZeroDilate R hR.ne' v) = timeZeroOneParticleInner m u v := by
  let F (m : ℝ) (u v : TimeZeroSource) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
    conj (timeZeroOneParticle m u p) * timeZeroOneParticle m v p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)
  have hpt (p : EuclideanSpace ℝ (Fin 3)) :
      F (m * R) (timeZeroDilate R hR.ne' u) (timeZeroDilate R hR.ne' v) (R • p) =
        ((R ^ 3)⁻¹ : ℝ) • F m u v p := by
    have hw : (1 / (2 * (2 * Real.pi) ^ 3 * dispersion (m * R) (R • p)) : ℝ) =
        R⁻¹ * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p)) := by
      rw [dispersion_smul m hR.le p]
      ring1
    have hc : ((R ^ 3)⁻¹ : ℝ) = R⁻¹ * R⁻¹ * R⁻¹ := by ring1
    dsimp only [F]
    rw [timeZeroOneParticle_dilate m hR u p, timeZeroOneParticle_dilate m hR v p,
      hw, hc, Complex.real_smul, map_mul, Complex.conj_ofReal]
    simp only [Complex.ofReal_mul]
    ring
  have hcov : (∫ p : EuclideanSpace ℝ (Fin 3),
      F (m * R) (timeZeroDilate R hR.ne' u) (timeZeroDilate R hR.ne' v) (R • p)) =
      |(R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))⁻¹| •
        timeZeroOneParticleInner (m * R) (timeZeroDilate R hR.ne' u)
          (timeZeroDilate R hR.ne' v) :=
    Measure.integral_comp_smul volume
      (F (m * R) (timeZeroDilate R hR.ne' u) (timeZeroDilate R hR.ne' v)) R
  have habs : |(R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))⁻¹| = (R ^ 3)⁻¹ := by
    rw [finrank_momentum]
    exact abs_of_pos (inv_pos.mpr (pow_pos hR 3))
  simp_rw [hpt] at hcov
  rw [integral_smul, habs] at hcov
  have h := congrArg (fun z : ℂ => (R ^ 3 : ℝ) • z) hcov
  simpa only [smul_inv_smul₀ (pow_ne_zero 3 hR.ne'), F, timeZeroOneParticleInner] using h.symm

theorem timeZeroOneParticleInner_re {m : ℝ} (hm : 0 < m) (u v : TimeZeroSource) :
    (timeZeroOneParticleInner m u v).re = timeZeroFourierCovariance m u v := by
  have h := congrArg Complex.re (timeZeroGram_identity hm u v)
  simpa [Complex.mul_re, Complex.div_re] using h

/-- Covariance preservation under the literal `(R² f(R·), R g(R·))` dilation. -/
theorem timeZeroFourierCovariance_dilate {m R : ℝ} (hm : 0 < m) (hR : 0 < R)
    (u v : TimeZeroSource) :
    timeZeroFourierCovariance (m * R) (timeZeroDilate R hR.ne' u)
      (timeZeroDilate R hR.ne' v) = timeZeroFourierCovariance m u v := by
  rw [← timeZeroOneParticleInner_re (mul_pos hm hR),
    timeZeroOneParticleInner_dilate m hR, timeZeroOneParticleInner_re hm]

end VacuumBellSeparation
