/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDilation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Spatial Fourier normalization and Parseval

The source uses `exp(-i p·x)`, whereas Mathlib uses `exp(-2π i p·x)`.
We prove the exact conversion and its three-dimensional Parseval factor.
These are analytic ingredients of (2.6); no time-slice or covariance identity
is an input to the definitions or proofs.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate FourierTransform SchwartzMap
open MeasureTheory

namespace VacuumBellSeparation

/-- A spatial test function, complexified as a genuine Schwartz function. -/
noncomputable def spatialSchwartz (f : SpatialTestFunction) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (f.2.2.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp f.2.1)

@[simp] theorem spatialSchwartz_apply (f : SpatialTestFunction)
    (x : EuclideanSpace ℝ (Fin 3)) : spatialSchwartz f x = (f.1 x : ℂ) := rfl

/-- Exact conversion from the source Fourier convention to Mathlib's convention. -/
theorem spatialFourier_two_pi (f : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    spatialFourier f ((2 * Real.pi) • p) = (𝓕 (spatialSchwartz f)) p := by
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [spatialSchwartz_apply, smul_eq_mul, real_inner_smul_left]
  congr 2
  rw [real_inner_comm x p]
  push_cast
  ring

/-- The source Fourier transform itself is Schwartz, with the normalization
implemented by an invertible continuous linear change of frequency. -/
noncomputable def spatialFourierSchwartz (f : SpatialTestFunction) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := EuclideanSpace ℝ (Fin 3))
      (Units.mk0 ((2 * Real.pi)⁻¹) (by positivity))) (𝓕 (spatialSchwartz f))

@[simp] theorem spatialFourierSchwartz_apply (f : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) : spatialFourierSchwartz f p = spatialFourier f p := by
  have h := spatialFourier_two_pi f ((2 * Real.pi)⁻¹ • p)
  change (𝓕 (spatialSchwartz f)) ((2 * Real.pi)⁻¹ • p) = spatialFourier f p
  simpa only [smul_smul, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0),
    one_smul] using h.symm

theorem continuous_spatialFourier (f : SpatialTestFunction) : Continuous (spatialFourier f) := by
  exact (spatialFourierSchwartz f).continuous.congr
    (fun p => spatialFourierSchwartz_apply f p)

/-- Every polynomially weighted Fourier norm is integrable. -/
theorem integrable_pow_norm_spatialFourier (f : SpatialTestFunction) (k : ℕ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖p‖ ^ k * ‖spatialFourier f p‖) := by
  simpa only [spatialFourierSchwartz_apply] using
    (spatialFourierSchwartz f).integrable_pow_mul volume k

/-- Polynomial weights times products of Fourier norms remain integrable. -/
theorem integrable_pow_norm_spatialFourier_product (f g : SpatialTestFunction) (k : ℕ) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (‖p‖ ^ k * ‖spatialFourier f p‖) * ‖spatialFourier g p‖) := by
  apply (integrable_pow_norm_spatialFourier f k).mul_bdd
    (continuous_spatialFourier g).norm.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    simpa only [norm_norm, spatialFourierSchwartz_apply] using
      (spatialFourierSchwartz g).norm_le_seminorm ℝ p

/-- Fourier products in the source convention are integrable. -/
theorem integrable_spatialFourier_product (f g : SpatialTestFunction) :
    Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      conj (spatialFourier f p) * spatialFourier g p) := by
  apply (integrable_comp_smul_iff volume _ (show 2 * Real.pi ≠ 0 by positivity)).mp
  simp_rw [spatialFourier_two_pi]
  simpa using ((𝓕 (spatialSchwartz f)).memLp 2).star.integrable_mul
    ((𝓕 (spatialSchwartz g)).memLp 2)

/-- Parseval with the manuscript's unnormalized transform and Lebesgue measures. -/
theorem integral_spatialFourier_product (f g : SpatialTestFunction) :
    (∫ p : EuclideanSpace ℝ (Fin 3),
      conj (spatialFourier f p) * spatialFourier g p) =
      (((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
        (∫ x : EuclideanSpace ℝ (Fin 3), (f.1 x : ℂ) * (g.1 x : ℂ)) := by
  have hparseval : (∫ p : EuclideanSpace ℝ (Fin 3),
      conj ((𝓕 (spatialSchwartz f)) p) * (𝓕 (spatialSchwartz g)) p) =
      ∫ x : EuclideanSpace ℝ (Fin 3), (f.1 x : ℂ) * (g.1 x : ℂ) := by
    simpa only [RCLike.inner_apply', spatialSchwartz_apply, Complex.conj_ofReal] using
      SchwartzMap.integral_inner_fourier_fourier (spatialSchwartz f) (spatialSchwartz g)
  have hcov := Measure.integral_comp_smul volume
    (fun p : EuclideanSpace ℝ (Fin 3) =>
      conj (spatialFourier f p) * spatialFourier g p) (2 * Real.pi)
  have hpos : 0 < (2 * Real.pi) ^ 3 := by positivity
  rw [finrank_momentum, abs_of_pos (inv_pos.mpr hpos)] at hcov
  simp_rw [spatialFourier_two_pi] at hcov
  rw [hparseval, Complex.real_smul] at hcov
  calc
    _ = ((((2 * Real.pi) ^ 3 : ℝ) : ℂ) *
        (((2 * Real.pi) ^ 3)⁻¹ : ℝ)) *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          conj (spatialFourier f p) * spatialFourier g p) := by
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
    _ = _ := by rw [mul_assoc, ← hcov]

end VacuumBellSeparation
