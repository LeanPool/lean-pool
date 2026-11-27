/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourLocalIntegral
public import LeanPool.VacuumBellSeparation.Shell.MeasurableContourWeights

/-!
# The actual local contour domination for all Borel ambient weights

The canonical preimage's strict energy and Lorentz bounds supply all
neighbourhood controls. The probability depends only on six Lorentz
parameters. The local comparison is uniform in nearby mass, retains
the physical energy cutoff, and has no assumed weight compatibility,
Jacobian bound, or image-cover hypothesis.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem actualContour_local_bound {Λ : Spacetime ≃L[ℝ] Spacetime}
    (hΛ : IsLorentzMap Λ) (m : ℝ) {B θ R : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ)
    (hE : radialShellEnergy m B 0 < R)
    (hn : spacetimeEuclideanOperatorNorm Λ < R)
    (hi : spacetimeEuclideanOperatorNorm Λ.symm < R) :
    ∃ ρ : ℝ, ∃ hρ : 0 < ρ,
      (∀ s : Fin 6 → ℝ, ‖s‖ ≤ ρ →
        spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s) < R ∧
        spacetimeEuclideanOperatorNorm (prefixedLorentzFamily Λ s).symm < R) ∧
      ∃ C δ d : ℝ, 0 < C ∧ 0 < δ ∧ 0 < d ∧
        ∀ τ : ℝ, |τ| < δ →
        ∀ F : ComplexSpacetime → ℝ≥0∞, Measurable F →
          ((ENNReal.ofReal d * ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R))) *
            (physicalParameterHaarScale : ℝ≥0∞) * volume (Metric.ball (0 : Fin 3 → ℝ) δ)) *
              (∫⁻ w in Metric.ball (referenceContourMap m B θ 0) δ,
                regularChartWeight (m + τ) Λ F w) ≤
            ((fixedMassContourHaarScale m hB hθ : ℝ≥0∞) * ENNReal.ofReal C) *
              ∫⁻ y, physicalContourCutoffWeight (m + τ) θ R Λ F y
                ∂(smoothBallProbability (Fin 6 → ℝ) ρ hρ).prod
                  (oneParticleMeasure (m + τ)) := by
  obtain ⟨ρ, hρ, hnorm⟩ := prefixedLorentzFamily_controlled_ball hΛ hn hi
  obtain ⟨rE, hrE, hcontrol⟩ := controlledContour_parameter_ball hΛ m hB hθ hE hn hi
  obtain ⟨rB, hrB, hbranch⟩ := fullContourPoint_branch_ball hB m θ
  let r₀ := min rE rB
  have hr₀ : 0 < r₀ := lt_min hrE hrB
  have he (q : ShellContourParameters) (hq : ‖q‖ < r₀) :
      0 < fullContourEnergy m B q ∧ fullContourEnergy m B q ≤ R := by
    have h := hcontrol q (hq.trans_le (min_le_left _ _))
    exact ⟨h.2.1, h.2.2.1.le⟩
  obtain ⟨r, C, δ, d, hr, hrr, hC, hδ, hd, hbound⟩ :=
    physicalContour_local_integral_bound m hB hθ hρ hr₀ he
  refine ⟨ρ, hρ, hnorm, C, δ, d, hC, hδ, hd, ?_⟩
  intro τ hτ F hF
  apply hbound τ hτ (regularChartWeight (m + τ) Λ F)
    (measurable_regularChartWeight_of_measurable _ _ hF)
    (physicalContourCutoffWeight (m + τ) θ R Λ F)
    (measurable_physicalContourCutoffWeight_of_measurable _ _ _ _ hF)
  intro q hq
  exact physicalContourCutoffWeight_chart_compatibility m hB hθ
    (fun x hx => hbranch x (hx.trans_le (hrr.trans (min_le_right _ _))))
    (fun x hx => (he x (hx.trans_le hrr)).2) Λ F τ hq

end VacuumBellSeparation
