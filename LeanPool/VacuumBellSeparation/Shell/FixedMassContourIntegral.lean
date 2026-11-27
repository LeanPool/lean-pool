/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.FixedMassContourImage
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The actual fixed-mass contour integral bound

The inverse function theorem supplies the rectangular image, the real
Jacobian theorem supplies the change of variables, and Tonelli supplies
the positive three-dimensional fibre volume. The determinant bound and
the rectangle are uniform in the nearby mass parameter. A prescribed
small source radius permits simultaneous geometric controls elsewhere.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal NNReal

instance fixedMassIntegral_sourceHaar :
    (volume : Measure ShellPhysicalParameters).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

instance fixedMassIntegral_targetHaar :
    ((volume : Measure (Fin 3 → ℂ)).prod
      (volume : Measure (Fin 3 → ℝ))).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Fixed mass contour Haar scale. -/
noncomputable def fixedMassContourHaarScale (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) : ℝ≥0 :=
  linearHaarScale (volume : Measure ShellPhysicalParameters)
    ((volume : Measure (Fin 3 → ℂ)).prod (volume : Measure (Fin 3 → ℝ)))
    (fixedMassContourLinearCoordinates m hB hθ)

theorem fixedMassContourHaarScale_pos (m : ℝ) {B θ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) :
    0 < fixedMassContourHaarScale m hB hθ := linearHaarScale_pos _ _ _

theorem fixedMassContour_ball_integral_bound (m : ℝ) {B θ r₀ : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (hr₀ : 0 < r₀) :
    ∃ r C δ : ℝ, 0 < r ∧ r ≤ r₀ ∧ 0 < C ∧ 0 < δ ∧
      ∀ τ : ℝ, |τ| < δ → ∀ g : (Fin 3 → ℂ) → ℝ≥0∞, Measurable g →
        (volume (Metric.ball (0 : Fin 3 → ℝ) δ)) *
            (∫⁻ w in Metric.ball (referenceContourMap m B θ 0) δ, g w) ≤
          (fixedMassContourHaarScale m hB hθ : ℝ≥0∞) * ENNReal.ofReal C *
            ∫⁻ q in fixedMassContourSmallDomain m hB hθ r τ,
              g (fullContourMap m B θ (fixedMassContourEmbedding τ q)) := by
  obtain ⟨rJ, C, hrJ, hC, hJ⟩ := fixedMassContour_uniform_jacobian_bound m hB hθ
  let r := min rJ r₀
  have hr : 0 < r := lt_min hrJ hr₀
  obtain ⟨δ, hδ, hcover⟩ := fixedMassContour_smallDomain_rectangle m hB hθ hr
  refine ⟨r, C, δ, hr, min_le_right _ _, hC, hδ, ?_⟩
  intro τ hτ g hg
  have hsmall (q : ShellPhysicalParameters)
      (hq : q ∈ fixedMassContourSmallDomain m hB hθ r τ) :
      ‖fixedMassContourEmbedding τ q‖ < rJ :=
    lt_of_lt_of_le hq.2 (min_le_left _ _)
  have hd (q : ShellPhysicalParameters)
      (hq : q ∈ fixedMassContourSmallDomain m hB hθ r τ) :=
    hJ (fixedMassContourEmbedding τ q) (hsmall q hq)
  exact rectangle_integral_le_jacobian_bound
    (volume : Measure ShellPhysicalParameters) (volume : Measure (Fin 3 → ℂ))
    (volume : Measure (Fin 3 → ℝ)) (fixedMassContourLinearCoordinates m hB hθ)
    (isOpen_fixedMassContourSmallDomain m hB hθ r τ).measurableSet
    (fun q hq => (hasFDerivAt_fixedMassContourMap m B θ τ q (hd q hq).1).hasFDerivWithinAt)
    ((fixedMassContourMap_injOn m hB hθ τ).mono (fun _ hq => hq.1))
    (fun q hq => (hd q hq).2) (hcover τ hτ) g hg

end VacuumBellSeparation
