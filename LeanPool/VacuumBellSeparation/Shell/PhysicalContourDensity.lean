/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.SmoothBallProbability
public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourParameterMeasure

/-!
# Positive physical product density on controlled contour parameters

The original mass-shell weight is retained exactly. Measurability holds
also at zero mass (the single zero-energy point has its defined weight
zero); the local lower bound explicitly requires positive energy.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem measurable_oneParticleWeight_all_mass (m : ℝ) :
    Measurable (oneParticleWeight m) :=
  continuous_real_toNNReal.measurable.comp
    (measurable_const.div (measurable_const.mul (continuous_dispersion m).measurable))

theorem oneParticleWeight_ennreal (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (oneParticleWeight m p : ℝ≥0∞) =
      ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p)) := rfl

theorem oneParticleWeight_lower_of_energy {m R : ℝ} {p : EuclideanSpace ℝ (Fin 3)}
    (hpos : 0 < dispersion m p) (hR : dispersion m p ≤ R) :
    ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R)) ≤
      (oneParticleWeight m p : ℝ≥0∞) := by
  rw [oneParticleWeight_ennreal]
  apply ENNReal.ofReal_le_ofReal
  apply one_div_le_one_div_of_le
  · positivity
  · exact mul_le_mul_of_nonneg_left hR (by positivity)

/-- Smooth physical contour density defined as `ENNReal.ofReal (smoothBallDensity (Fin 6 → ℝ) r hr
q.1) * (oneParticleWeight m q.2 : ℝ≥0∞)`. -/
noncomputable def smoothPhysicalContourDensity (m r : ℝ) (hr : 0 < r)
    (q : LorentzMomentumParameters) : ℝ≥0∞ :=
  ENNReal.ofReal (smoothBallDensity (Fin 6 → ℝ) r hr q.1) *
    (oneParticleWeight m q.2 : ℝ≥0∞)

theorem measurable_smoothPhysicalContourDensity (m r : ℝ) (hr : 0 < r) :
    Measurable (smoothPhysicalContourDensity m r hr) :=
  (((contDiff_smoothBallDensity (Fin 6 → ℝ) r hr).continuous.measurable.comp
    measurable_fst).ennreal_ofReal).mul
      (((measurable_oneParticleWeight_all_mass m).comp measurable_snd).coe_nnreal_ennreal)

theorem smoothPhysicalContour_product_measure (m r : ℝ) (hr : 0 < r) :
    (smoothBallProbability (Fin 6 → ℝ) r hr).prod (oneParticleMeasure m) =
      physicalParameterMeasure.withDensity (smoothPhysicalContourDensity m r hr) := by
  exact prod_withDensity
    (contDiff_smoothBallDensity (Fin 6 → ℝ) r hr).continuous.measurable.ennreal_ofReal
    (measurable_oneParticleWeight_all_mass m).coe_nnreal_ennreal

theorem smoothPhysicalContour_density_lower (m r : ℝ) (hr : 0 < r) :
    ∃ d > 0, ∀ R : ℝ, ∀ q : LorentzMomentumParameters,
      ‖q.1‖ ≤ r / 2 → 0 < dispersion m q.2 → dispersion m q.2 ≤ R →
        ENNReal.ofReal d * ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R)) ≤
          smoothPhysicalContourDensity m r hr q := by
  obtain ⟨d, hd, hinner⟩ := smoothBallDensity_constant_on_inner (Fin 6 → ℝ) r hr
  refine ⟨d, hd, fun R q hq hpos hR => ?_⟩
  rw [smoothPhysicalContourDensity, hinner q.1 hq]
  exact _root_.mul_le_mul_right (oneParticleWeight_lower_of_energy hpos hR) _

theorem smoothPhysicalContour_integral_lower (m r : ℝ) (hr : 0 < r) :
    ∃ d > 0, ∀ R : ℝ, ∀ s : Set LorentzMomentumParameters,
      MeasurableSet s →
      (∀ q ∈ s, ‖q.1‖ ≤ r / 2 ∧ 0 < dispersion m q.2 ∧ dispersion m q.2 ≤ R) →
      ∀ g : LorentzMomentumParameters → ℝ≥0∞, Measurable g →
        (ENNReal.ofReal d * ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R))) *
            (∫⁻ q in s, g q ∂physicalParameterMeasure) ≤
          ∫⁻ q in s, g q ∂(smoothBallProbability (Fin 6 → ℝ) r hr).prod
            (oneParticleMeasure m) := by
  obtain ⟨d, hd, hlower⟩ := smoothPhysicalContour_density_lower m r hr
  refine ⟨d, hd, fun R s hs hcontrol g hg => ?_⟩
  rw [smoothPhysicalContour_product_measure,
    setLIntegral_withDensity_eq_setLIntegral_mul _
      (measurable_smoothPhysicalContourDensity m r hr) hg hs,
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  exact setLIntegral_mono' hs (fun q hq => _root_.mul_le_mul_left
    (hlower R q (hcontrol q hq).1 (hcontrol q hq).2.1 (hcontrol q hq).2.2) _)

end VacuumBellSeparation
