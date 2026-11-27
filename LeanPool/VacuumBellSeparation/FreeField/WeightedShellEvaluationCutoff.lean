/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WeightedShellEvaluationContourAE
public import LeanPool.VacuumBellSeparation.Shell.UniformContourSubmean

/-!
# Removing the actual shell energy cutoff by the exact damping factor

This comparison uses the physical cutoff omega <= 32/sin(theta).
All integrals are nonnegative extended integrals, so no finiteness is
assumed before the source-weight estimate is applied.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ENNReal

theorem cutoff_damping_bound {θ E L t : ℝ} (hθ : 0 < Real.sin θ)
    (hE : 0 ≤ E) (hL : 0 ≤ L) {N : ℕ}
    (D : Fin N → ControlledContourPatch θ) (u v : TimeZeroSource)
    (y : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3)) :
    contourMixtureCutoffWeight t D
      (fun z => ENNReal.ofReal (‖scaledComplexTestWave E u v z‖ ^ 2)) y ≤
        ENNReal.ofReal (Real.exp (2 * L * E * (32 / Real.sin θ) * Real.sin θ)) *
          ENNReal.ofReal (scaledComplexTestContourIntegrand t E L θ
            (contourMixtureFamily D y.1) u v y.2) := by
  classical
  by_cases hy : dispersion t y.2 ≤ 32 / Real.sin θ
  · rw [contourMixtureCutoffWeight, Set.indicator_of_mem (s := {z : (Fin N × (Fin 6
      → ℝ)) × EuclideanSpace ℝ (Fin 3) |
      dispersion t z.2 ≤ 32 / Real.sin θ}) hy]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    unfold scaledComplexTestContourIntegrand
    have hb : 2 * L * E * dispersion t y.2 * Real.sin θ ≤
        2 * L * E * (32 / Real.sin θ) * Real.sin θ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hy (by positivity)) hθ.le
    have he : 1 ≤ Real.exp (2 * L * E * (32 / Real.sin θ) * Real.sin θ) *
        Real.exp (-2 * L * E * dispersion t y.2 * Real.sin θ) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      linarith
    simpa only [contourMixturePoint, mul_assoc, one_mul] using
      mul_le_mul_of_nonneg_right he
        (sq_nonneg ‖scaledComplexTestWave E u v (contourMixturePoint t D y)‖)
  · rw [contourMixtureCutoffWeight, Set.indicator_of_notMem (s := {z : (Fin N × (Fin 6
      → ℝ)) × EuclideanSpace ℝ (Fin 3) |
      dispersion t z.2 ≤ 32 / Real.sin θ}) hy]
    exact bot_le

theorem contourMixture_cutoff_lintegral_le_damped {θ E L t : ℝ}
    (hθ : 0 < Real.sin θ) (hE : 0 ≤ E) (hL : 0 ≤ L) {N : ℕ}
    (D : Fin N → ControlledContourPatch θ) (u v : TimeZeroSource) :
    (∫⁻ y, contourMixtureCutoffWeight t D
      (fun z => ENNReal.ofReal (‖scaledComplexTestWave E u v z‖ ^ 2)) y
        ∂(contourMixtureProbability D).prod (oneParticleMeasure t)) ≤
      ENNReal.ofReal (Real.exp (2 * L * E * (32 / Real.sin θ) * Real.sin θ)) *
        ∫⁻ a, ∫⁻ p, ENNReal.ofReal (scaledComplexTestContourIntegrand t E L θ
          (contourMixtureFamily D a) u v p) ∂oneParticleMeasure t
            ∂contourMixtureProbability D := by
  let _ : SigmaFinite (oneParticleMeasure t) := by unfold oneParticleMeasure; infer_instance
  have hm : Measurable (fun y : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) =>
      ENNReal.ofReal (scaledComplexTestContourIntegrand t E L θ
        (contourMixtureFamily D y.1) u v y.2)) := by
    apply ENNReal.measurable_ofReal.comp
    apply Continuous.measurable
    unfold scaledComplexTestContourIntegrand
    have hd := (continuous_dispersion t).comp
      (continuous_snd : Continuous fun y :
        (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) => y.2)
    have he : Continuous (fun y : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) =>
        Real.exp (-2 * L * E * dispersion t y.2 * Real.sin θ)) := by fun_prop
    exact he.mul (((differentiable_scaledComplexTestWave E u v).continuous.comp
      (continuous_contourMixturePoint t D)).norm.pow 2)
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (2 * L * E * (32 / Real.sin θ) * Real.sin θ)) *
        ENNReal.ofReal (scaledComplexTestContourIntegrand t E L θ
          (contourMixtureFamily D y.1) u v y.2)
          ∂(contourMixtureProbability D).prod (oneParticleMeasure t) :=
      lintegral_mono (cutoff_damping_bound hθ hE hL D u v)
    _ = _ := by
      rw [lintegral_const_mul _ hm, lintegral_prod _ hm.aemeasurable]

end VacuumBellSeparation
