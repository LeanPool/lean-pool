/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourDensity

/-!
# Mass-uniform physical density and the exact damping loss

The positive parameter-density constant is chosen before the mass.
Consequently the local comparison is uniform through zero normalized
mass. The damping comparison retains the literal exponential in the
physical energy cutoff, for use in the manuscript's fixed exponent.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem smoothPhysicalContour_uniform_integral_lower (r : ℝ) (hr : 0 < r) :
    ∃ d > 0, ∀ m R : ℝ, ∀ s : Set LorentzMomentumParameters,
      MeasurableSet s →
      (∀ q ∈ s, ‖q.1‖ ≤ r / 2 ∧ 0 < dispersion m q.2 ∧ dispersion m q.2 ≤ R) →
      ∀ g : LorentzMomentumParameters → ℝ≥0∞, Measurable g →
        (ENNReal.ofReal d * ENNReal.ofReal (1 / (2 * (2 * Real.pi) ^ 3 * R))) *
            (∫⁻ q in s, g q ∂physicalParameterMeasure) ≤
          ∫⁻ q in s, g q ∂(smoothBallProbability (Fin 6 → ℝ) r hr).prod
            (oneParticleMeasure m) := by
  obtain ⟨d, hd, hinner⟩ := smoothBallDensity_constant_on_inner (Fin 6 → ℝ) r hr
  refine ⟨d, hd, fun m R s hs hcontrol g hg => ?_⟩
  rw [smoothPhysicalContour_product_measure,
    setLIntegral_withDensity_eq_setLIntegral_mul _
      (measurable_smoothPhysicalContourDensity m r hr) hg hs,
    ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
  apply setLIntegral_mono' hs
  intro q hq
  apply _root_.mul_le_mul_left
  rw [smoothPhysicalContourDensity, hinner q.1 (hcontrol q hq).1]
  exact _root_.mul_le_mul_right
    (oneParticleWeight_lower_of_energy (hcontrol q hq).2.1 (hcontrol q hq).2.2) _

theorem energyDamping_lower {m a R : ℝ} (ha : 0 ≤ a)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : dispersion m p ≤ R) :
    ENNReal.ofReal (Real.exp (-a * R)) ≤
      ENNReal.ofReal (Real.exp (-a * dispersion m p)) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr ha)

theorem energyDamping_set_integral_lower {m a R : ℝ} (ha : 0 ≤ a)
    (μ : Measure LorentzMomentumParameters) {s : Set LorentzMomentumParameters}
    (hs : MeasurableSet s) (henergy : ∀ q ∈ s, dispersion m q.2 ≤ R)
    (g : LorentzMomentumParameters → ℝ≥0∞) :
    ENNReal.ofReal (Real.exp (-a * R)) * (∫⁻ q in s, g q ∂μ) ≤
      ∫⁻ q in s, ENNReal.ofReal (Real.exp (-a * dispersion m q.2)) * g q ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact setLIntegral_mono' hs (fun q hq =>
    _root_.mul_le_mul_left (energyDamping_lower ha (henergy q hq)) _)

end VacuumBellSeparation
