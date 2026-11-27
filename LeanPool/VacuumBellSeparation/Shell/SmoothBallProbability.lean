/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# A genuine smooth parameter probability on any prescribed ball

This density is in the Lorentz parameter variables alone. Its product
with the original physical momentum measure therefore retains the
product structure required by the averaged wedge estimate.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure
    (volume : Measure E)]

/-- Smooth ball bump defined as `r / 2 rOut := r rIn_pos := half_pos hr rIn_lt_rOut := half_lt_self
hr`. -/
noncomputable def smoothBallBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : E) where
  rIn := r / 2
  rOut := r
  rIn_pos := half_pos hr
  rIn_lt_rOut := half_lt_self hr

/-- Normalize the smooth radial bump on the radius-`r` ball to a probability density. -/
noncomputable def smoothBallDensity (r : ℝ) (hr : 0 < r) : E → ℝ :=
  (smoothBallBump E r hr).normed volume

/-- Smooth ball probability defined as `volume.withDensity (fun x => ENNReal.ofReal
(smoothBallDensity E r hr x))`. -/
noncomputable def smoothBallProbability (r : ℝ) (hr : 0 < r) : Measure E :=
  volume.withDensity (fun x => ENNReal.ofReal (smoothBallDensity E r hr x))

omit [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
theorem smoothBallDensity_nonneg (r : ℝ) (hr : 0 < r) (x : E) :
    0 ≤ smoothBallDensity E r hr x := (smoothBallBump E r hr).nonneg_normed x

omit [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
theorem contDiff_smoothBallDensity (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothBallDensity E r hr) := (smoothBallBump E r hr).contDiff_normed

theorem smoothBallDensity_integral (r : ℝ) (hr : 0 < r) :
    ∫ x, smoothBallDensity E r hr x = 1 := (smoothBallBump E r hr).integral_normed

instance smoothBallProbability_isProbability (r : ℝ) (hr : 0 < r) :
    IsProbabilityMeasure (smoothBallProbability E r hr) where
  measure_univ := by
    rw [smoothBallProbability, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    change (∫⁻ x, ENNReal.ofReal ((smoothBallBump E r hr).normed volume x)) = 1
    rw [← ofReal_integral_eq_lintegral_ofReal
      (smoothBallBump E r hr).integrable_normed
      (Filter.Eventually.of_forall (smoothBallDensity_nonneg E r hr)),
      (smoothBallBump E r hr).integral_normed, ENNReal.ofReal_one]

theorem smoothBallDensity_support (r : ℝ) (hr : 0 < r) :
    Function.support (smoothBallDensity E r hr) = Metric.ball 0 r :=
  (smoothBallBump E r hr).support_normed_eq

theorem smoothBallDensity_hasCompactSupport (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (smoothBallDensity E r hr) :=
  (smoothBallBump E r hr).hasCompactSupport_normed

theorem smoothBallDensity_constant_on_inner (r : ℝ) (hr : 0 < r) :
    ∃ d > 0, ∀ x : E, ‖x‖ ≤ r / 2 → smoothBallDensity E r hr x = d := by
  let b := smoothBallBump E r hr
  refine ⟨1 / ∫ x, b x, one_div_pos.mpr b.integral_pos, ?_⟩
  intro x hx
  have hb : b x = 1 := b.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right, b, smoothBallBump] using hx)
  change b x / (∫ x, b x) = _
  rw [hb]

theorem smoothBallProbability_compl_ball (r : ℝ) (hr : 0 < r) :
    smoothBallProbability E r hr (Metric.ball 0 r)ᶜ = 0 := by
  rw [smoothBallProbability, withDensity_apply _ Metric.isOpen_ball.measurableSet.compl]
  apply setLIntegral_eq_zero Metric.isOpen_ball.measurableSet.compl
  intro x hx
  have hz : smoothBallDensity E r hr x = 0 := by
    by_contra hn
    exact hx ((smoothBallDensity_support E r hr) ▸ hn)
  simp only [hz, ENNReal.ofReal_zero, Pi.zero_apply]

end VacuumBellSeparation
