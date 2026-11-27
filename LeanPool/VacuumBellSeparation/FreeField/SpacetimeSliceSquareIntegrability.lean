/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpacetimePartialFourier
public import LeanPool.VacuumBellSeparation.FreeField.SpatialMassShellBound

/-!
# Actual joint square integrability of the evolved spatial slices

The physical mass-shell Parseval bound is integrated in time. Compactness
and continuity of the original spacetime source prove integrability of its
square before Fubini is applied. No uniform Fourier derivative estimate or
Schwartz-valued integral is required.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter

private theorem integrable_sq_of_continuous_compact
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (f : X → ℝ) (hf : Continuous f) (hs : HasCompactSupport f) :
    Integrable (fun y => f y ^ 2) μ :=
  (hf.pow 2).integrable_of_hasCompactSupport
    (hs.comp_left (g := fun a : ℝ => a ^ 2) (zero_pow (by decide)))

theorem integrable_spacetimeTest_sq (F : RealTestFunction) :
    Integrable (fun y : Spacetime => F.1 y ^ 2) :=
  integrable_sq_of_continuous_compact volume F.1 F.2.1.continuous F.2.2

theorem integrable_spacetimePartialFourier_sq {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) :
    Integrable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
      ‖spacetimePartialFourier F z.1 z.2‖ ^ 2) (volume.prod (oneParticleMeasure m)) := by
  let := oneParticleMeasure_isLocallyFinite hm
  have hmeas : AEStronglyMeasurable
      (fun z : ℝ × EuclideanSpace ℝ (Fin 3) => ‖spacetimePartialFourier F z.1 z.2‖ ^ 2)
      (volume.prod (oneParticleMeasure m)) :=
    ((continuous_spacetimePartialFourier F).norm.pow 2).aestronglyMeasurable
  have hbound : Integrable (fun t : ℝ => (1 / (2 * m)) *
      ∫ x : EuclideanSpace ℝ (Fin 3), F.1 (t, x) ^ 2) :=
    (integrable_spacetimeTest_sq F).integral_prod_left.const_mul _
  have hout : Integrable (fun t : ℝ =>
      ∫ p, ‖spacetimePartialFourier F t p‖ ^ 2 ∂oneParticleMeasure m) := by
    apply hbound.mono' hmeas.integral_prod_right'
    exact Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (integral_nonneg fun p => sq_nonneg _)]
      exact integral_spatialFourier_norm_sq_massShell_le hm (spacetimeSpatialSlice F t)
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · exact Eventually.of_forall fun t =>
      integrable_spatialFourier_norm_sq_massShell hm (spacetimeSpatialSlice F t)
  · simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hout

theorem integrable_spacetimeEvolvedFourier_sq {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) :
    Integrable (fun z : ℝ × EuclideanSpace ℝ (Fin 3) =>
      ‖spacetimeEvolvedFourier m F z.1 z.2‖ ^ 2) (volume.prod (oneParticleMeasure m)) := by
  simpa only [norm_spacetimeEvolvedFourier] using integrable_spacetimePartialFourier_sq hm F

end VacuumBellSeparation
