/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourSourceControl
public import LeanPool.VacuumBellSeparation.Shell.UniformPhysicalContourDensity
public import LeanPool.VacuumBellSeparation.Shell.FixedMassContourIntegral

/-!
# Local shell-coordinate control by the actual physical product measure

Every geometric cover and Jacobian hypothesis is supplied by the actual
contour inverse. The remaining weight compatibility is explicit, so the
theorem applies to both ambient test weights and the energy-cutoff wave
integrand. All constants are chosen before the nearby mass and weight.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem physicalContour_local_integral_bound (m : ℝ) {B θ ρ r₀ R : ℝ}
    (hB : 0 < B) (hθ : 0 < Real.sin θ) (hρ : 0 < ρ) (hr₀ : 0 < r₀)
    (henergy : ∀ q : ShellContourParameters, ‖q‖ < r₀ →
      0 < fullContourEnergy m B q ∧ fullContourEnergy m B q ≤ R) :
    ∃ r C δ d : ℝ, 0 < r ∧ r ≤ r₀ ∧ 0 < C ∧ 0 < δ ∧ 0 < d ∧
      ∀ τ : ℝ, |τ| < δ →
      ∀ g : (Fin 3 → ℂ) → ℝ≥0∞, Measurable g →
      ∀ G : LorentzMomentumParameters → ℝ≥0∞, Measurable G →
      (∀ q ∈ fixedMassContourSmallDomain m hB hθ r τ,
        G (physicalContourParameters B q) =
          g (fullContourMap m B θ (fixedMassContourEmbedding τ q))) →
        ((ENNReal.ofReal d * ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R))) *
          (physicalParameterHaarScale : ℝ≥0∞) * volume (Metric.ball (0 : Fin 3 → ℝ) δ)) *
            (∫⁻ w in Metric.ball (referenceContourMap m B θ 0) δ, g w) ≤
          ((fixedMassContourHaarScale m hB hθ : ℝ≥0∞) * ENNReal.ofReal C) *
            ∫⁻ y, G y ∂(smoothBallProbability (Fin 6 → ℝ) ρ hρ).prod
              (oneParticleMeasure (m + τ)) := by
  obtain ⟨r, C, δ, hr, hrr, hC, hδ, hcoord⟩ :=
    fixedMassContour_ball_integral_bound m hB hθ (lt_min hr₀ (half_pos hρ))
  obtain ⟨d, hd, hphysical⟩ := smoothPhysicalContour_uniform_integral_lower ρ hρ
  have hrr₀ : r ≤ r₀ := hrr.trans (min_le_left _ _)
  have hrrρ : r ≤ ρ / 2 := hrr.trans (min_le_right _ _)
  refine ⟨r, C, δ, d, hr, hrr₀, hC, hδ, hd, ?_⟩
  intro τ hτ g hg G hG hmatch
  let s := fixedMassContourSmallDomain m hB hθ r τ
  let t := physicalContourParameters B '' s
  let k : ℝ≥0∞ := ENNReal.ofReal d * ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R))
  let A : ℝ≥0∞ := (fixedMassContourHaarScale m hB hθ : ℝ≥0∞) * ENNReal.ofReal C
  let P : ℝ≥0∞ := physicalParameterHaarScale
  let J := ∫⁻ q in s, g (fullContourMap m B θ (fixedMassContourEmbedding τ q))
  have hs : MeasurableSet s := (isOpen_fixedMassContourSmallDomain m hB hθ r τ).measurableSet
  have ht : MeasurableSet t := (isOpen_physicalContourSmallImage m hB hθ r τ).measurableSet
  have hcontrol : ∀ y ∈ t,
      ‖y.1‖ ≤ ρ / 2 ∧ 0 < dispersion (m + τ) y.2 ∧ dispersion (m + τ) y.2 ≤ R :=
    physicalContourSmallImage_control m hB hθ hrrρ
      (fun q hq => henergy q (hq.trans_le hrr₀)) τ
  have him : (∫⁻ y in t, G y ∂physicalParameterMeasure) = P * J := by
    rw [lintegral_physicalContourParameters_image B hs]
    apply congrArg (fun x : ℝ≥0∞ => P * x)
    exact setLIntegral_congr_fun hs hmatch
  have hphys : k * (P * J) ≤
      ∫⁻ y, G y ∂(smoothBallProbability (Fin 6 → ℝ) ρ hρ).prod
        (oneParticleMeasure (m + τ)) := by
    have h := hphysical (m + τ) R t ht hcontrol G hG
    rw [him] at h
    exact h.trans (lintegral_mono' Measure.restrict_le_self (le_refl G))
  have hc : volume (Metric.ball (0 : Fin 3 → ℝ) δ) *
      (∫⁻ w in Metric.ball (referenceContourMap m B θ 0) δ, g w) ≤ A * J :=
    hcoord τ hτ g hg
  calc
    _ = (k * P) * (volume (Metric.ball (0 : Fin 3 → ℝ) δ) *
        (∫⁻ w in Metric.ball (referenceContourMap m B θ 0) δ, g w)) := by
          simp only [k, P, mul_assoc]
    _ ≤ (k * P) * (A * J) := _root_.mul_le_mul_right hc _
    _ = A * (k * (P * J)) := by ac_rfl
    _ ≤ _ := _root_.mul_le_mul_right hphys A

end VacuumBellSeparation
