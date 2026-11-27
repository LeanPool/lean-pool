/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SchwartzEvolution
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# The actual dispersion-graph measure for spacetime evolution

The Fourier frequency graph is `(-h(ξ)/(2π), -ξ)`. Pushing forward Lebesgue
measure onto this graph permits direct reuse of the general Fourier-integral
smoothness theorem. Every required moment is proved integrable using actual
Schwartz multipliers and ordinary Schwartz momentum moments.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter
open scoped FourierTransform InnerProductSpace

/-- Positive-signature coordinate pairing between two spacetime vectors. -/
noncomputable def spacetimeEuclideanPairing : Spacetime →L[ℝ] Spacetime →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
      (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin 3))) +
    (show Spacetime →L[ℝ] Spacetime →L[ℝ] ℝ from
      (innerSL ℝ (E := EuclideanSpace ℝ (Fin 3)) :
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3)))
      (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin 3))))

@[simp] theorem spacetimeEuclideanPairing_apply (p x : Spacetime) :
    spacetimeEuclideanPairing p x = p.1 * x.1 + ⟪p.2, x.2⟫_ℝ := rfl

/-- Evolution graph time. -/
noncomputable def evolutionGraphTime (m : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  -massiveSchwartzSymbol m 1 ξ / (2 * Real.pi)

theorem hasTemperateGrowth_evolutionGraphTime (m : ℝ) :
    Function.HasTemperateGrowth (evolutionGraphTime m) := by
  simpa only [evolutionGraphTime, div_eq_mul_inv, Pi.mul_apply, Pi.neg_apply] using!
    (hasTemperateGrowth_massiveSchwartzSymbol m 1).neg.mul
      (Function.HasTemperateGrowth.const (2 * Real.pi)⁻¹)

/-- Evolution frequency graph. -/
noncomputable def evolutionFrequencyGraph (m : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) : Spacetime :=
  (evolutionGraphTime m ξ, -ξ)

theorem continuous_evolutionFrequencyGraph (m : ℝ) : Continuous (evolutionFrequencyGraph m) :=
  (hasTemperateGrowth_evolutionGraphTime m).1.continuous.prodMk continuous_id.neg

/-- Evolution graph measure obtained from `Measure.map`. -/
noncomputable def evolutionGraphMeasure (m : ℝ) : Measure Spacetime :=
  Measure.map (evolutionFrequencyGraph m) volume

theorem integrable_evolutionGraphTime_moment (m : ℝ) (φ : SpatialSchwartz) (n : ℕ) :
    Integrable (fun ξ => ‖evolutionGraphTime m ξ‖ ^ n * ‖φ ξ‖) := by
  have ht : Function.HasTemperateGrowth (fun ξ => (evolutionGraphTime m ξ : ℂ) ^ n) :=
    (Complex.hasTemperateGrowth_ofReal.comp (hasTemperateGrowth_evolutionGraphTime m)).pow n
  have hi := (SchwartzMap.smulLeftCLM ℂ (fun ξ =>
    (evolutionGraphTime m ξ : ℂ) ^ n) φ).integrable (μ := volume) |>.norm
  simpa only [SchwartzMap.smulLeftCLM_apply_apply ht, smul_eq_mul,
    norm_mul, norm_pow, Complex.norm_real] using hi

theorem integrable_evolutionFrequencyGraph_moment (m : ℝ) (φ : SpatialSchwartz) (n : ℕ) :
    Integrable (fun ξ => ‖evolutionFrequencyGraph m ξ‖ ^ n * ‖φ ξ‖) := by
  have hi := (integrable_evolutionGraphTime_moment m φ n).add (φ.integrable_pow_mul volume n)
  apply hi.mono'
    (((continuous_evolutionFrequencyGraph m).norm.pow n).mul φ.continuous.norm).aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    change ‖(‖evolutionFrequencyGraph m ξ‖ ^ n * ‖φ ξ‖ : ℝ)‖ ≤
      ‖evolutionGraphTime m ξ‖ ^ n * ‖φ ξ‖ + ‖ξ‖ ^ n * ‖φ ξ‖
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    simp only [evolutionFrequencyGraph, Prod.norm_mk, norm_neg]
    rcases le_total ‖evolutionGraphTime m ξ‖ ‖ξ‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (by positivity)

/-- All actual moments of the amplitude against the pushed-forward graph
measure are finite; no smoothness theorem is assumed in this statement. -/
theorem integrable_evolutionGraphMeasure_moment (m : ℝ) (φ : SpatialSchwartz) (n : ℕ) :
    Integrable (fun p : Spacetime => ‖p‖ ^ n * ‖φ (-p.2)‖) (evolutionGraphMeasure m) := by
  have hc : Continuous (fun p : Spacetime => ‖p‖ ^ n * ‖φ (-p.2)‖) :=
    (continuous_id.norm.pow n).mul (φ.continuous.comp continuous_snd.neg).norm
  apply (integrable_map_measure hc.aestronglyMeasurable
    (continuous_evolutionFrequencyGraph m).measurable.aemeasurable).mpr
  simpa only [Function.comp_def, evolutionFrequencyGraph, neg_neg] using
    integrable_evolutionFrequencyGraph_moment m φ n

/-- Spacetime phase evolution. -/
noncomputable def spacetimePhaseEvolution (m : ℝ) (φ : SpatialSchwartz) : Spacetime → ℂ :=
  VectorFourier.fourierIntegral 𝐞 (evolutionGraphMeasure m)
    spacetimeEuclideanPairing.toLinearMap₁₂ (fun p => φ (-p.2))

/-- Genuine joint spacetime smoothness, obtained from the proved graph moments. -/
theorem contDiff_spacetimePhaseEvolution (m : ℝ) (φ : SpatialSchwartz) :
    ContDiff ℝ (⊤ : ℕ∞) (spacetimePhaseEvolution m φ) :=
  VectorFourier.contDiff_fourierIntegral spacetimeEuclideanPairing
    (fun n _ => integrable_evolutionGraphMeasure_moment m φ n)

theorem spacetimePhaseEvolution_eq_integral (m : ℝ) (φ : SpatialSchwartz) (x : Spacetime) :
    spacetimePhaseEvolution m φ x =
      ∫ ξ, (𝐞 (-spacetimeEuclideanPairing (evolutionFrequencyGraph m ξ) x) : ℂ) * φ ξ := by
  unfold spacetimePhaseEvolution VectorFourier.fourierIntegral evolutionGraphMeasure
  rw [integral_map (continuous_evolutionFrequencyGraph m).measurable.aemeasurable]
  · apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by
      simp only [evolutionFrequencyGraph, neg_neg, Circle.smul_def, smul_eq_mul]
      rfl
  · apply Continuous.aestronglyMeasurable
    exact ((Real.continuous_fourierChar.comp
      ((spacetimeEuclideanPairing.flip x).continuous.neg)).smul
        (φ.continuous.comp continuous_snd.neg))

end VacuumBellSeparation
