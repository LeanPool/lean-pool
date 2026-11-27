/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.HaarJacobianBound
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Quantitative rectangular-fibre estimate

Tonelli supplies the actual fibre measure. Together with a genuine
Jacobian bound and an actual rectangle contained in the image this
controls the integral over the free shell coordinates.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

variable {E F N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace N] [BorelSpace N]
  (μ : Measure E) (ν : Measure F) (η : Measure N)
  [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] [η.IsAddHaarMeasure]

omit [BorelSpace F] [BorelSpace N] in
theorem lintegral_rectangle_first (s : Set F) (t : Set N)
    (g : F → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in s ×ˢ t, g y.1 ∂ν.prod η) = (η t) * ∫⁻ w in s, g w ∂ν := by
  rw [setLIntegral_prod (fun y : F × N => g y.1)
    (show AEMeasurable (fun y : F × N => g y.1) ((ν.prod η).restrict (s ×ˢ t)) from
      (hg.comp measurable_fst).aemeasurable)]
  simp only [lintegral_const, Measure.restrict_apply_univ]
  rw [lintegral_mul_const _ hg, mul_comm]

theorem rectangle_integral_le_jacobian_bound (J : E ≃L[ℝ] F × N)
    {f : E → F × N} {f' : E → E →L[ℝ] F × N} {s : Set E}
    (hs : MeasurableSet s) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hinj : Set.InjOn f s) {C : ℝ}
    (hC : ∀ x ∈ s, |(J.symm.toContinuousLinearMap.comp (f' x)).det| ≤ C)
    {u : Set F} {v : Set N} (hcover : u ×ˢ v ⊆ f '' s)
    (g : F → ℝ≥0∞) (hg : Measurable g) :
    (η v) * (∫⁻ w in u, g w ∂ν) ≤
      (linearHaarScale μ (ν.prod η) J : ℝ≥0∞) * ENNReal.ofReal C *
        ∫⁻ x in s, g (f x).1 ∂μ := by
  rw [← lintegral_rectangle_first ν η u v g hg]
  exact lintegral_subset_image_le_linearHaarScale_jacobian_bound μ (ν.prod η)
    J hs hf' hinj hC hcover (fun y => g y.1)

end VacuumBellSeparation
