/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CompactLaplace
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDilation

/-!
# Entire slices of the literal spatial Fourier transform

The real axis of this entire function is exactly `spatialFourier f (p + t a)`
in the manuscript's unnormalized Fourier convention. This constructs the
analytic function used in the odd-order argument for compact test sources.
-/

@[expose] public section

open scoped InnerProductSpace
open MeasureTheory

namespace VacuumBellSeparation

/-- Spatial Fourier slice. -/
noncomputable def spatialFourierSlice (f : SpatialTestFunction)
    (p a : EuclideanSpace ℝ (Fin 3)) : ℂ → ℂ :=
  compactExpTransform (fun x => -(Complex.I * (⟪a, x⟫_ℝ : ℂ)))
    (fun x => Complex.exp (-(Complex.I * (⟪p, x⟫_ℝ : ℂ))) * (f.1 x : ℂ))

theorem analyticOnNhd_spatialFourierSlice (f : SpatialTestFunction)
    (p a : EuclideanSpace ℝ (Fin 3)) :
    AnalyticOnNhd ℂ (spatialFourierSlice f p a) Set.univ := by
  apply analyticOnNhd_compactExpTransform
  · exact (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id))).neg
  · exact (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (continuous_const.inner continuous_id))).neg).mul
      (Complex.continuous_ofReal.comp f.2.1.continuous)
  · exact (f.2.2.comp_left Complex.ofReal_zero).mul_left

theorem spatialFourierSlice_ofReal (f : SpatialTestFunction)
    (p a : EuclideanSpace ℝ (Fin 3)) (t : ℝ) :
    spatialFourierSlice f p a (t : ℂ) = spatialFourier f (p + t • a) := by
  unfold spatialFourierSlice compactExpTransform spatialFourier
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  dsimp only
  rw [← mul_assoc, ← Complex.exp_add, inner_add_left, real_inner_smul_left]
  congr 2
  push_cast
  ring

end VacuumBellSeparation
