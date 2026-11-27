/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.EvolutionSpacetimeSmooth
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Actual pointwise time derivatives of the massive evolution

The graph Fourier derivative is differentiated using its proved zeroth and
first absolute moments. Evaluating the resulting continuous linear map in
the time direction gives the actual multiplier `i h`. This supplies scalar
pointwise derivatives independently of the earlier L² argument.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter FourierTransform
open scoped FourierTransform

theorem integrable_evolutionGraph_amplitude (m : ℝ) (φ : SpatialSchwartz) :
    Integrable (fun p : Spacetime => φ (-p.2)) (evolutionGraphMeasure m) := by
  apply (integrable_norm_iff
    (φ.continuous.comp continuous_snd.neg).aestronglyMeasurable).mp
  simpa only [pow_zero, one_mul, Function.comp_apply, Pi.neg_apply] using
    integrable_evolutionGraphMeasure_moment m φ 0

theorem integrable_evolutionGraph_fourierSMulRight (m : ℝ) (φ : SpatialSchwartz) :
    Integrable (VectorFourier.fourierSMulRight spacetimeEuclideanPairing
      (fun p : Spacetime => φ (-p.2))) (evolutionGraphMeasure m) := by
  have hi : Integrable (fun p : Spacetime => ‖p‖ * ‖φ (-p.2)‖) (evolutionGraphMeasure m) := by
    simpa only [pow_one] using integrable_evolutionGraphMeasure_moment m φ 1
  apply (hi.const_mul (2 * Real.pi * ‖spacetimeEuclideanPairing‖)).mono'
    (integrable_evolutionGraph_amplitude m φ).1.fourierSMulRight
  exact Eventually.of_forall fun p => by
    simpa only [mul_assoc] using VectorFourier.norm_fourierSMulRight_le
      spacetimeEuclideanPairing (fun p : Spacetime => φ (-p.2)) p

theorem evolutionGraph_fourierSMulRight_time (m : ℝ) (φ : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    VectorFourier.fourierSMulRight spacetimeEuclideanPairing
      (fun p : Spacetime => φ (-p.2)) (evolutionFrequencyGraph m ξ) (1, 0) =
        (Complex.I • massiveFrequencyEnergy m φ) ξ := by
  simp only [VectorFourier.fourierSMulRight_apply, spacetimeEuclideanPairing_apply,
    evolutionFrequencyGraph, evolutionGraphTime, neg_neg, inner_zero_right,
    mul_one, add_zero, smul_apply, massiveFrequencyEnergy_apply,
    smul_eq_mul, Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]


theorem evolutionGraph_time_derivative_integral (m t : ℝ) (φ : SpatialSchwartz)
    (x : EuclideanSpace ℝ (Fin 3)) :
    VectorFourier.fourierIntegral 𝐞 (evolutionGraphMeasure m)
      spacetimeEuclideanPairing.toLinearMap₁₂
      (VectorFourier.fourierSMulRight spacetimeEuclideanPairing (fun p : Spacetime => φ (-p.2)))
      (t, x) (1, 0) = spacetimePhaseEvolution m (Complex.I • massiveFrequencyEnergy m φ) (t,
        x) := by
  have hi := integrable_evolutionGraph_fourierSMulRight m φ
  rw [Real.fourierIntegral_continuousLinearMap_apply' hi]
  have hphase := (Real.fourierIntegral_convergent_iff' spacetimeEuclideanPairing (t, x)).mpr
    (hi.apply_continuousLinearMap (1, 0))
  rw [VectorFourier.fourierIntegral, evolutionGraphMeasure]
  change (∫ v : Spacetime, 𝐞 (-spacetimeEuclideanPairing v (t, x)) •
    (VectorFourier.fourierSMulRight spacetimeEuclideanPairing
      (fun p : Spacetime => φ (-p.2)) v) (1, 0)
      ∂Measure.map (evolutionFrequencyGraph m) volume) = _
  rw [integral_map (continuous_evolutionFrequencyGraph m).measurable.aemeasurable hphase.1,
    spacetimePhaseEvolution_eq_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    change (𝐞 (-spacetimeEuclideanPairing (evolutionFrequencyGraph m ξ) (t, x)) : ℂ) *
        VectorFourier.fourierSMulRight spacetimeEuclideanPairing
          (fun p : Spacetime => φ (-p.2)) (evolutionFrequencyGraph m ξ) (1, 0) =
      (𝐞 (-spacetimeEuclideanPairing (evolutionFrequencyGraph m ξ) (t, x)) : ℂ) *
        (Complex.I • massiveFrequencyEnergy m φ) ξ
    exact congrArg (fun z : ℂ =>
      (𝐞 (-spacetimeEuclideanPairing (evolutionFrequencyGraph m ξ) (t, x)) : ℂ) * z)
      (evolutionGraph_fourierSMulRight_time m φ ξ)

theorem hasDerivAt_spacetimePhaseEvolution_time (m t : ℝ) (φ : SpatialSchwartz)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => spacetimePhaseEvolution m φ (s, x))
      (spacetimePhaseEvolution m (Complex.I • massiveFrequencyEnergy m φ) (t, x)) t := by
  have hi : Integrable (fun p : Spacetime => ‖p‖ * ‖φ (-p.2)‖) (evolutionGraphMeasure m) := by
    simpa only [pow_one] using integrable_evolutionGraphMeasure_moment m φ 1
  have h := (VectorFourier.hasFDerivAt_fourierIntegral spacetimeEuclideanPairing
    (integrable_evolutionGraph_amplitude m φ) hi (t, x)).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  simp only [Function.comp_def, id_eq, evolutionGraph_time_derivative_integral] at h
  change HasDerivAt (fun s => spacetimePhaseEvolution m φ (s, x))
    (spacetimePhaseEvolution m (Complex.I • massiveFrequencyEnergy m φ) (t, x)) t at h
  exact h

theorem spacetimePhaseEvolution_smul (m : ℝ) (c : ℂ) (φ : SpatialSchwartz) (x : Spacetime) :
    spacetimePhaseEvolution m (c • φ) x = c * spacetimePhaseEvolution m φ x := by
  simp only [spacetimePhaseEvolution_eq_integral, smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun _ => by ring

theorem massiveFrequencyEnergy_fourier (m : ℝ) (f : SpatialSchwartz) :
    massiveFrequencyEnergy m (𝓕 f) = 𝓕 (massiveSchwartzPower m 1 f) := by
  rw [massiveSchwartzPower, SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq]
  rfl

/-- The actual scalar pointwise derivative of the literal spatial evolution. -/
theorem hasDerivAt_massiveSchwartzEvolution_pointwise (m t : ℝ) (f : SpatialSchwartz)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveSchwartzEvolution m s f x)
      (Complex.I * massiveSchwartzEvolution m t (massiveSchwartzPower m 1 f) x) t := by
  simpa only [spacetimePhaseEvolution_fourier_eq, spacetimePhaseEvolution_smul,
    massiveFrequencyEnergy_fourier] using hasDerivAt_spacetimePhaseEvolution_time m t (𝓕 f) x

theorem hasDerivAt_massiveSchwartzEvolution_neg_pointwise (m t : ℝ) (f : SpatialSchwartz)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveSchwartzEvolution m (-s) f x)
      (-(Complex.I * massiveSchwartzEvolution m (-t) (massiveSchwartzPower m 1 f) x)) t := by
  simpa only [Function.comp_def, neg_one_smul] using
    (hasDerivAt_massiveSchwartzEvolution_pointwise m (-t) f x).scomp t (hasDerivAt_neg t)

theorem hasDerivAt_massiveSchwartzCauchy_pointwise (m t : ℝ) (f g : SpatialSchwartz)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveSchwartzCauchy m s f g x)
      (massiveSchwartzCauchyVelocity m t f g x) t := by
  have h := (hasDerivAt_massiveSchwartzEvolution_pointwise m t (cauchyPositiveData m f g) x).add
    (hasDerivAt_massiveSchwartzEvolution_neg_pointwise m t (cauchyNegativeData m f g) x)
  simpa only [massiveSchwartzCauchy_eq_phases, add_apply,
    massiveSchwartzCauchyVelocity, sub_apply, smul_apply,
    smul_eq_mul, sub_eq_add_neg, neg_apply, smul_apply,
    smul_eq_mul, Pi.add_def] using h

end VacuumBellSeparation
