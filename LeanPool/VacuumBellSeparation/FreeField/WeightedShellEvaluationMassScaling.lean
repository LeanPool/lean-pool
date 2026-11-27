/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Dilation
public import LeanPool.VacuumBellSeparation.Shell.PhysicalContourDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The actual mass-shell E² scaling

The original density is retained, including its zero value at the
zero-energy point when the normalized mass is zero. Positive dilation
of the real three-dimensional momentum volume and the exact reciprocal
dispersion scaling give the mass-shell factor E². All integrals are
nonnegative extended integrals, so no finiteness is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped ENNReal

theorem oneParticleWeight_dilation (m : ℝ) {E : ℝ} (hE : 0 < E)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (oneParticleWeight (m * E) (E • p) : ℝ≥0∞) =
      ENNReal.ofReal E⁻¹ * (oneParticleWeight m p : ℝ≥0∞) := by
  rw [oneParticleWeight_ennreal, oneParticleWeight_ennreal,
    dispersion_smul m hE.le]
  have hreal : 1 / (2 * (2 * Real.pi) ^ 3 * (E * dispersion m p)) =
      E⁻¹ * (1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hreal, ENNReal.ofReal_mul (inv_nonneg.mpr hE.le)]

theorem lintegral_oneParticle_dilation (m : ℝ) {E : ℝ} (hE : 0 < E)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hf : Measurable f) :
    ENNReal.ofReal (E ^ 2) *
        (∫⁻ p, f (E • p) ∂oneParticleMeasure m) =
      ∫⁻ p, f p ∂oneParticleMeasure (m * E) := by
  have hw (t : ℝ) : Measurable (fun p : EuclideanSpace ℝ (Fin 3) =>
      (oneParticleWeight t p : ℝ≥0∞)) :=
    (measurable_oneParticleWeight_all_mass t).coe_nnreal_ennreal
  have hdil : Measurable (fun p : EuclideanSpace ℝ (Fin 3) => E • p) :=
    measurable_const_smul E
  have hcov : (∫⁻ p : EuclideanSpace ℝ (Fin 3),
      (oneParticleWeight (m * E) (E • p) : ℝ≥0∞) * f (E • p)) =
      ENNReal.ofReal ((E ^ 3)⁻¹) *
        (∫⁻ p : EuclideanSpace ℝ (Fin 3), (oneParticleWeight (m * E) p : ℝ≥0∞) * f p) := by
    calc
      _ = ∫⁻ p : EuclideanSpace ℝ (Fin 3),
          (oneParticleWeight (m * E) p : ℝ≥0∞) * f p
            ∂Measure.map (fun p : EuclideanSpace ℝ (Fin 3) => E • p) volume := by
        simpa only [Pi.mul_apply] using
          (lintegral_map (μ := volume) ((hw (m * E)).mul hf) hdil).symm
      _ = _ := by
        rw [Measure.map_addHaar_smul volume hE.ne', lintegral_smul_measure,
          finrank_momentum, abs_of_pos (inv_pos.mpr (pow_pos hE 3)), smul_eq_mul]
  simp_rw [oneParticleWeight_dilation m hE, mul_assoc] at hcov
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hcov
  have hleft : ENNReal.ofReal (E ^ 3) * ENNReal.ofReal E⁻¹ = ENNReal.ofReal (E ^ 2) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hE.le 3)]
    congr 1
    rw [show E ^ 3 = E ^ 2 * E by ring, mul_assoc, mul_inv_cancel₀ hE.ne', mul_one]
  have hright : ENNReal.ofReal (E ^ 3) * ENNReal.ofReal ((E ^ 3)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hE.le 3),
      mul_inv_cancel₀ (pow_ne_zero 3 hE.ne'), ENNReal.ofReal_one]
  have h := congrArg (fun x : ℝ≥0∞ => ENNReal.ofReal (E ^ 3) * x) hcov
  rw [← mul_assoc, hleft, ← mul_assoc, hright, one_mul] at h
  have hwm : (∫⁻ p, f (E • p) ∂oneParticleMeasure m) =
      ∫⁻ p : EuclideanSpace ℝ (Fin 3), (oneParticleWeight m p : ℝ≥0∞) * f (E • p) := by
    simpa only [oneParticleMeasure, Function.comp_def, Pi.mul_apply] using
      lintegral_withDensity_eq_lintegral_mul volume (hw m) (hf.comp hdil)
  have hwme : (∫⁻ p, f p ∂oneParticleMeasure (m * E)) =
      ∫⁻ p : EuclideanSpace ℝ (Fin 3), (oneParticleWeight (m * E) p : ℝ≥0∞) * f p := by
    simpa only [oneParticleMeasure, Pi.mul_apply] using
      lintegral_withDensity_eq_lintegral_mul volume (hw (m * E)) hf
  rw [hwm, hwme]
  exact h

/-- The physical scaling survives averaging over any actual parameter
measure; no product-measure finiteness is needed for this iterated form. -/
theorem averaged_lintegral_oneParticle_dilation {A : Type*} [MeasurableSpace A]
    (ν : Measure A) (m : ℝ) {E : ℝ} (hE : 0 < E)
    (f : A → EuclideanSpace ℝ (Fin 3) → ℝ≥0∞)
    (hf : ∀ a, Measurable (f a)) :
    ENNReal.ofReal (E ^ 2) *
        (∫⁻ a, ∫⁻ p, f a (E • p) ∂oneParticleMeasure m ∂ν) =
      ∫⁻ a, ∫⁻ p, f a p ∂oneParticleMeasure (m * E) ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro a
  exact lintegral_oneParticle_dilation m hE (f a) (hf a)

end VacuumBellSeparation
