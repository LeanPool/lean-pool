/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourSourceControl
public import LeanPool.VacuumBellSeparation.Shell.ControlledLorentzProbability
public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceContinuity

/-!
# Actual measurable shell-chart and energy-cutoff contour weights

The principal chart is used only on its proven open branch; its weight
is extended by zero elsewhere. The physical weight uses the literal
Lorentz contour and the manuscript's physical energy cutoff.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

/-- Regular chart weight. -/
noncomputable def regularChartWeight (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (F : ComplexSpacetime → ℝ≥0∞) : (Fin 3 → ℂ) → ℝ≥0∞ := by
  classical
  exact (complexShellChartDomain m).piecewise (fun w => F (lorentzComplexShellChart m Λ w)) 0

theorem measurable_regularChartWeight (m : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    {F : ComplexSpacetime → ℝ≥0∞} (hF : Continuous F) :
    Measurable (regularChartWeight m Λ F) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuous_const.continuousOn
    (isOpen_complexShellChartDomain m).measurableSet
  intro w hw
  exact hF.continuousAt.comp_continuousWithinAt
    (differentiableAt_lorentzComplexShellChart Λ hw).continuousAt.continuousWithinAt

theorem regularChartWeight_eq {m : ℝ} (Λ : Spacetime ≃L[ℝ] Spacetime)
    (F : ComplexSpacetime → ℝ≥0∞) {w : Fin 3 → ℂ} (hw : w ∈ complexShellChartDomain m) :
    regularChartWeight m Λ F w = F (lorentzComplexShellChart m Λ w) := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hw

/-- Physical contour point defined as `complexifiedSpacetimeMap (prefixedLorentzFamily Λ y.1)
(complexShellBoost m ((θ : ℂ) * Complex.I) y.2)`. -/
noncomputable def physicalContourPoint (m θ : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime)
    (y : LorentzMomentumParameters) : ComplexSpacetime :=
  complexifiedSpacetimeMap (prefixedLorentzFamily Λ y.1)
    (complexShellBoost m ((θ : ℂ) * Complex.I) y.2)

theorem continuous_physicalContourPoint (m θ : ℝ) (Λ : Spacetime ≃L[ℝ] Spacetime) :
    Continuous (physicalContourPoint m θ Λ) := by
  have hpair : Continuous (fun q : LorentzMomentumParameters =>
      (q.1, complexShellBoost m ((θ : ℂ) * Complex.I) q.2)) :=
    (continuous_fst : Continuous
      (Prod.fst : LorentzMomentumParameters → (Fin 6 → ℝ))).prodMk
      ((continuous_complexShellBoost m ((θ : ℂ) * Complex.I)).comp continuous_snd)
  exact Continuous.comp'
    (f := fun q : LorentzMomentumParameters =>
      (q.1, complexShellBoost m ((θ : ℂ) * Complex.I) q.2))
    (g := fun q : (Fin 6 → ℝ) × ComplexSpacetime =>
      complexifiedSpacetimeMap (prefixedLorentzFamily Λ q.1) q.2)
    (continuous_complexifiedSpacetimeMap_family (prefixedLorentzFamily Λ)
      (continuous_prefixedLorentzFamily_apply Λ)) hpair

/-- Physical contour cutoff weight. -/
noncomputable def physicalContourCutoffWeight (m θ R : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (F : ComplexSpacetime → ℝ≥0∞) :
    LorentzMomentumParameters → ℝ≥0∞ :=
  {y | dispersion m y.2 ≤ R}.indicator (fun y => F (physicalContourPoint m θ Λ y))

theorem measurable_physicalContourCutoffWeight (m θ R : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) {F : ComplexSpacetime → ℝ≥0∞} (hF : Continuous F) :
    Measurable (physicalContourCutoffWeight m θ R Λ F) :=
  (hF.comp (continuous_physicalContourPoint m θ Λ)).measurable.indicator
    (isClosed_le ((continuous_dispersion m).comp continuous_snd) continuous_const).measurableSet

theorem physicalContourCutoffWeight_chart_compatibility (m : ℝ) {B θ r R : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ)
    (hbranch : ∀ q : ShellContourParameters, ‖q‖ < r →
      0 < ((fullContourPoint m B θ q).2 1).re ∧
      fullContourMap m B θ q ∈ complexShellChartDomain (m + q.2.1))
    (henergy : ∀ q : ShellContourParameters, ‖q‖ < r → fullContourEnergy m B q ≤ R)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (F : ComplexSpacetime → ℝ≥0∞) (τ : ℝ)
    {q : ShellPhysicalParameters} (hq : q ∈ fixedMassContourSmallDomain m hB hθ r τ) :
    physicalContourCutoffWeight (m + τ) θ R Λ F (physicalContourParameters B q) =
      regularChartWeight (m + τ) Λ F
        (fullContourMap m B θ (fixedMassContourEmbedding τ q)) := by
  have hb := hbranch (fixedMassContourEmbedding τ q) hq.2
  have he : dispersion (m + τ) (physicalContourParameters B q).2 ≤ R := by
    rw [physicalContourParameters_momentum B τ]
    exact (fullContourEnergy_eq_dispersion m B (fixedMassContourEmbedding τ q)) ▸ henergy _ hq.2
  have hbchart : fullContourMap m B θ (fixedMassContourEmbedding τ q) ∈
      complexShellChartDomain (m + τ) := hb.2
  rw [physicalContourCutoffWeight,
    Set.indicator_of_mem (show physicalContourParameters B q ∈
      {y : LorentzMomentumParameters | dispersion (m + τ) y.2 ≤ R} from he),
    regularChartWeight_eq Λ F hbchart]
  apply congrArg F
  exact (physicalContourSmallImage_chart_identity m hB hθ
    (fun q hq => (hbranch q hq).1) Λ τ hq).symm

end VacuumBellSeparation
