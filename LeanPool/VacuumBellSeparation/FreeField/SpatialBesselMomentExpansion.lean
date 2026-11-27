/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialKernelMomentSeries

/-!
# Original covariance kernels as actual sums of test moments

Both the coefficient bound and the full pointwise series are discharged
by the Bessel/Cauchy construction. The hypotheses specify only the
actual compact tests, coordinate support and geometric separation.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian MeasureTheory

theorem hasSum_spatialFieldBessel_moments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialFieldMultiCoefficient μ s R k.1 k.2 * spatialTestMoment f k.1 * spatialTestMoment g
        k.2)
      (∫ xy, (spatialFieldBesselKernel μ (spatialAxisDisplacement s (xy.2 - xy.1)) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume) := by
  apply hasSum_spatialKernelMoments hR
    (show 0 ≤ spatialFieldPolydiscBound μ s R by unfold spatialFieldPolydiscBound; positivity)
    (fun k => spatialFieldMultiCoefficient μ s R k.1 k.2)
    (fun x y => (spatialFieldBesselKernel μ (spatialAxisDisplacement s (y - x)) : ℂ))
    (fun k => spatialFieldMultiCoefficient_norm_le hμ hs hR hsep k.1 k.2)
    (fun x y hx hy => spatialFieldMultiCoefficient_real_expansion hμ hs hR hsep x y hx hy)
    f g hf hg

theorem hasSum_spatialMomentumBessel_moments {μ s R : ℝ}
    (hμ : 0 < μ) (hs : 0 < s) (hR : 0 < R) (hsep : 8 * Real.sqrt 3 * R ≤ s)
    (f g : SpatialTestFunction)
    (hf : ∀ x, f.1 x ≠ 0 → ∀ j, ‖x j‖ ≤ R / 2)
    (hg : ∀ y, g.1 y ≠ 0 → ∀ j, ‖y j‖ ≤ R / 2) :
    HasSum (fun k : (Fin 3 → ℕ) × (Fin 3 → ℕ) =>
      spatialMomentumMultiCoefficient μ s R k.1 k.2 * spatialTestMoment f k.1 *
        spatialTestMoment g k.2)
      (∫ xy, (spatialMomentumBesselKernel μ (spatialAxisDisplacement s (xy.2 - xy.1)) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume) := by
  apply hasSum_spatialKernelMoments hR
    (show 0 ≤ spatialMomentumPolydiscBound μ s R by unfold spatialMomentumPolydiscBound; positivity)
    (fun k => spatialMomentumMultiCoefficient μ s R k.1 k.2)
    (fun x y => (spatialMomentumBesselKernel μ (spatialAxisDisplacement s (y - x)) : ℂ))
    (fun k => spatialMomentumMultiCoefficient_norm_le hμ hs hR hsep k.1 k.2)
    (fun x y hx hy => spatialMomentumMultiCoefficient_real_expansion hμ hs hR hsep x y hx hy)
    f g hf hg

end VacuumBellSeparation
