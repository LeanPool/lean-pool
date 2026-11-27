/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialCovarianceMomentExpansion

/-!
# Real moments and the real part of the actual kernel coefficients

The original tests are real. Their moments are real, so the true covariance
series uses the real parts of the contour coefficients without requiring an
additional coefficient-reality theorem.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory
open scoped BigOperators

/-- Spatial real test moment given by `∫ x, (∏ j, x j ^ α j) * f.1 x`. -/
noncomputable def spatialRealTestMoment (f : SpatialTestFunction) (α : Fin 3 → ℕ) : ℝ :=
  ∫ x, (∏ j, x j ^ α j) * f.1 x

theorem spatialTestMoment_eq_ofReal (f : SpatialTestFunction) (α : Fin 3 → ℕ) :
    spatialTestMoment f α = (spatialRealTestMoment f α : ℂ) := by
  unfold spatialTestMoment spatialMonomial spatialRealTestMoment
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by push_cast; rfl

theorem spatialRealTestMoment_norm_le {a : ℝ}
    (f : SpatialTestFunction) (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ a)
    (α : Fin 3 → ℕ) :
    |spatialRealTestMoment f α| ≤ a ^ (∑ j, α j) * ∫ x, ‖f.1 x‖ := by
  simpa only [spatialTestMoment_eq_ofReal, Complex.norm_real, Real.norm_eq_abs] using
    spatialTestMoment_norm_le f hf α

theorem hasSum_timeZeroCovariance_realMoments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (u v : TimeZeroSource)
    (huf : ∀ x, u.1.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hug : ∀ x, u.2.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hvf : ∀ x, v.1.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hvg : ∀ x, v.2.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      (spatialFieldMultiCoefficient μ s R k.1 k.2).re * spatialRealTestMoment u.1 k.1 *
          spatialRealTestMoment v.1 k.2 +
        (spatialMomentumMultiCoefficient μ s R k.1 k.2).re * spatialRealTestMoment u.2 k.1 *
          spatialRealTestMoment v.2 k.2)
      (timeZeroFourierCovariance μ u (timeZeroTranslate (spatialAxisDisplacement s 0) v)) := by
  simpa only [spatialTestMoment_eq_ofReal, Complex.add_re, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul,
    sub_zero, add_zero] using
    hasSum_timeZeroCovariance_moments hμ hs hR hsep u v huf hug hvf hvg

end VacuumBellSeparation
