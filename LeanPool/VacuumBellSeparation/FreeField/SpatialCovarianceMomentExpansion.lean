/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialKernelTranslation

/-!
# Actual original Fourier covariance as a convergent moment series

The kernels, Cauchy coefficients, moments, translation and Fourier
normalization all refer to the original source definitions. No kernel
expansion or covariance factorization appears as a hypothesis here.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory
open scoped ComplexConjugate

theorem hasSum_spatialFourier_field_moments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialFieldMultiCoefficient μ s R k.1 k.2 * spatialTestMoment f k.1 * spatialTestMoment g
        k.2)
      (((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) *
        (∫ p : EuclideanSpace ℝ (Fin 3), ((dispersion μ p)⁻¹ : ℝ) *
          (conj (spatialFourier f p) *
            spatialFourier (spatialTestTranslate (spatialAxisDisplacement s 0) g) p))) := by
  rw [spatialFourier_translated_field_kernel hμ hR hsep f g hf hg]
  exact hasSum_spatialFieldBessel_moments hμ hs hR hsep f g hf hg

theorem hasSum_spatialFourier_momentum_moments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialMomentumMultiCoefficient μ s R k.1 k.2 * spatialTestMoment f k.1 *
        spatialTestMoment g k.2)
      (((1 / (2 * (2 * Real.pi) ^ 3) : ℝ) : ℂ) *
        (∫ p : EuclideanSpace ℝ (Fin 3), (dispersion μ p : ℂ) *
          (conj (spatialFourier f p) *
            spatialFourier (spatialTestTranslate (spatialAxisDisplacement s 0) g) p))) := by
  rw [spatialFourier_translated_momentum_kernel hμ hR hsep f g hf hg]
  exact hasSum_spatialMomentumBessel_moments hμ hs hR hsep f g hf hg

theorem hasSum_timeZeroCovariance_moments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (u v : TimeZeroSource)
    (huf : ∀ x, u.1.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hug : ∀ x, u.2.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hvf : ∀ x, v.1.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hvg : ∀ x, v.2.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      (spatialFieldMultiCoefficient μ s R k.1 k.2 * spatialTestMoment u.1 k.1 *
          spatialTestMoment v.1 k.2 +
        spatialMomentumMultiCoefficient μ s R k.1 k.2 * spatialTestMoment u.2 k.1 *
          spatialTestMoment v.2 k.2).re)
      (timeZeroFourierCovariance μ u (timeZeroTranslate (spatialAxisDisplacement s 0) v)) := by
  have hf := hasSum_spatialFourier_field_moments hμ hs hR hsep u.1 v.1 huf hvf
  have hg := hasSum_spatialFourier_momentum_moments hμ hs hR hsep u.2 v.2 hug hvg
  have h := Complex.hasSum_re (hf.add hg)
  convert h using 1
  unfold timeZeroFourierCovariance timeZeroFourierDiagonal timeZeroTranslate
  congr 1
  simp only [mul_add, mul_comm]

theorem hasSum_timeZeroOneParticle_real_moments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (u v : TimeZeroSource)
    (huf : ∀ x, u.1.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hug : ∀ x, u.2.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hvf : ∀ x, v.1.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hvg : ∀ x, v.2.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      (spatialFieldMultiCoefficient μ s R k.1 k.2 * spatialTestMoment u.1 k.1 *
          spatialTestMoment v.1 k.2 +
        spatialMomentumMultiCoefficient μ s R k.1 k.2 * spatialTestMoment u.2 k.1 *
          spatialTestMoment v.2 k.2).re)
      (timeZeroOneParticleInner μ u (timeZeroTranslate (spatialAxisDisplacement s 0) v)).re := by
  rw [timeZeroGram_identity hμ]
  simpa using hasSum_timeZeroCovariance_moments hμ hs hR hsep u v huf hug hvf hvg

end VacuumBellSeparation
