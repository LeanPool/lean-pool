/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialFourier
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Frequency normalization for actual tempered distributions

The source convention uses `exp(-i p·x)`. To apply Mathlib's inverse Fourier
transform, its momentum distribution must represent `ξ ↦ F(2πξ)`. The
transpose of inverse test scaling includes the actual three-dimensional
Jacobian; this file proves its value on regular Schwartz distributions.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace VacuumBellSeparation

/-- Actual positive scalar change of coordinates in three-dimensional Schwartz space. -/
noncomputable def spatialSchwartzScale (c : ℝ) (hc : 0 < c) :
    SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ →L[ℂ]
      SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := EuclideanSpace ℝ (Fin 3))
      (Units.mk0 c hc.ne'))

@[simp] theorem spatialSchwartzScale_apply (c : ℝ) (hc : 0 < c)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    spatialSchwartzScale c hc φ p = φ (c • p) := rfl

/-- Distributional scaling representing `F(c·)`, including its Jacobian. -/
noncomputable def spatialDistributionScale (c : ℝ) (hc : 0 < c) :
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ →L[ℂ]
      TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (((c ^ 3)⁻¹ : ℝ) : ℂ) • PointwiseConvergenceCLM.precomp ℂ
    (spatialSchwartzScale c⁻¹ (inv_pos.mpr hc))

theorem spatialDistributionScale_apply (c : ℝ) (hc : 0 < c)
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    spatialDistributionScale c hc T φ =
      (((c ^ 3)⁻¹ : ℝ) : ℂ) * T (spatialSchwartzScale c⁻¹ (inv_pos.mpr hc) φ) := rfl

/-- The transpose and Jacobian produce the claimed literal regular distribution. -/
theorem spatialDistributionScale_coe (c : ℝ) (hc : 0 < c)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    spatialDistributionScale c hc (f : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) =
      (spatialSchwartzScale c hc f :
        TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  ext φ
  rw [spatialDistributionScale_apply, SchwartzMap.coe_apply, SchwartzMap.coe_apply]
  simp only [spatialSchwartzScale_apply, smul_eq_mul]
  have h := Measure.integral_comp_smul volume
    (fun p : EuclideanSpace ℝ (Fin 3) => φ (c⁻¹ • p) * f p) c
  rw [finrank_momentum, abs_of_pos (inv_pos.mpr (pow_pos hc 3)), Complex.real_smul] at h
  simpa only [inv_smul_smul₀ hc.ne'] using h.symm

/-- Convert the source frequency convention and then apply the actual inverse Fourier map. -/
noncomputable def sourceInverseFourier :
    TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ →L[ℂ]
      TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (FourierTransform.fourierInvCLM ℂ _).comp
    (spatialDistributionScale (2 * Real.pi) (by positivity))

theorem sourceInverseFourier_apply
    (T : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) :
    sourceInverseFourier T =
      𝓕⁻ (spatialDistributionScale (2 * Real.pi) (by positivity) T) := rfl

/-- On literal compact sources the complete normalization returns the original
position-space function, as an actual tempered distribution. -/
theorem sourceInverseFourier_spatialFourier (f : SpatialTestFunction) :
    sourceInverseFourier (spatialFourierSchwartz f :
      TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) =
      (spatialSchwartz f : TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ) := by
  have hscale : spatialSchwartzScale (2 * Real.pi) (by positivity)
      (spatialFourierSchwartz f) = 𝓕 (spatialSchwartz f) := by
    ext ξ
    simp only [spatialSchwartzScale_apply, spatialFourierSchwartz_apply,
      spatialFourier_two_pi]
  rw [sourceInverseFourier_apply, spatialDistributionScale_coe, hscale,
    ← TemperedDistribution.fourier_toTemperedDistributionCLM_eq,
    FourierTransform.fourierInv_fourier_eq]

end VacuumBellSeparation
