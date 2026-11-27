/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.MassShellDistribution
public import LeanPool.VacuumBellSeparation.FreeField.SchwartzKleinGordon

/-!
# Removing the physical mass-shell density

The reciprocal density is a genuine temperate multiplier for positive mass.
Multiplying the physical distribution by it gives a continuous, injective
embedding whose pairing is the unweighted momentum integral. Integrability of
that pairing is proved separately from the identity for the Bochner integral.
-/

@[expose] public section

open MeasureTheory
open scoped SchwartzMap

namespace VacuumBellSeparation

theorem hasTemperateGrowth_dispersion {m : ℝ} (hm : 0 < m) :
    Function.HasTemperateGrowth (dispersion m) := by
  have h := (hasTemperateGrowth_massiveSchwartzSymbol m 1).comp
    (show Function.HasTemperateGrowth
      (fun p : EuclideanSpace ℝ (Fin 3) => (2 * Real.pi)⁻¹ • p) by fun_prop)
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  simpa only [Function.comp_def, massiveSchwartzSymbol_one hm,
    smul_inv_smul₀ hc] using h

theorem hasTemperateGrowth_inv_dispersion {m : ℝ} (hm : 0 < m) :
    Function.HasTemperateGrowth (fun p => (dispersion m p)⁻¹) := by
  have h := (hasTemperateGrowth_massiveSchwartzSymbol m (-1)).comp
    (show Function.HasTemperateGrowth
      (fun p : EuclideanSpace ℝ (Fin 3) => (2 * Real.pi)⁻¹ • p) by fun_prop)
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  simpa only [Function.comp_def, massiveSchwartzSymbol_neg_one hm,
    smul_inv_smul₀ hc] using h

/-- The reciprocal of the literal physical mass-shell density. -/
noncomputable def inverseShellDensity (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ((2 * (2 * Real.pi) ^ 3 : ℝ) : ℂ) * (dispersion m p : ℂ)

/-- The literal physical mass-shell density, viewed as a complex multiplier. -/
noncomputable def complexShellDensity (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  (((2 * (2 * Real.pi) ^ 3)⁻¹ : ℝ) : ℂ) * ((dispersion m p)⁻¹ : ℝ)

theorem hasTemperateGrowth_inverseShellDensity {m : ℝ} (hm : 0 < m) :
    Function.HasTemperateGrowth (inverseShellDensity m) :=
  (Function.HasTemperateGrowth.const _).mul
    (Complex.ofRealCLM.hasTemperateGrowth.comp (hasTemperateGrowth_dispersion hm))

theorem hasTemperateGrowth_complexShellDensity {m : ℝ} (hm : 0 < m) :
    Function.HasTemperateGrowth (complexShellDensity m) :=
  (Function.HasTemperateGrowth.const _).mul
    (Complex.ofRealCLM.hasTemperateGrowth.comp (hasTemperateGrowth_inv_dispersion hm))

theorem complexShellDensity_eq_weight {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    complexShellDensity m p = ((oneParticleWeight m p : ℝ) : ℂ) := by
  rw [oneParticleWeight_coe hm]
  simp [complexShellDensity, one_div, mul_inv_rev, mul_comm]

theorem inverseShellDensity_mul_density {m : ℝ} (hm : 0 < m)
    (p : EuclideanSpace ℝ (Fin 3)) :
    inverseShellDensity m p * complexShellDensity m p = 1 := by
  have hω : dispersion m p ≠ 0 := (hm.trans_le (le_dispersion hm.le p)).ne'
  have hc : (2 * (2 * Real.pi) ^ 3 : ℝ) ≠ 0 := by positivity
  simp only [inverseShellDensity, complexShellDensity, Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hc, Complex.ofReal_ne_zero.mpr hω]

/-- The actual unweighted momentum distribution of a physical one-particle vector. -/
noncomputable def unweightedMomentumDistribution {m : ℝ} (hm : 0 < m) :
    Lp ℂ 2 (oneParticleMeasure m) →L[ℂ] TemperedDistribution (EuclideanSpace ℝ (Fin 3)) ℂ :=
  (TemperedDistribution.smulLeftCLM ℂ (inverseShellDensity m)).comp
    (physicalMomentumDistribution hm)

theorem reweight_unweightedMomentumDistribution {m : ℝ} (hm : 0 < m)
    (u : Lp ℂ 2 (oneParticleMeasure m)) :
    TemperedDistribution.smulLeftCLM ℂ (complexShellDensity m)
      (unweightedMomentumDistribution hm u) = physicalMomentumDistribution hm u := by
  change TemperedDistribution.smulLeftCLM ℂ (complexShellDensity m)
      (TemperedDistribution.smulLeftCLM ℂ (inverseShellDensity m)
        (physicalMomentumDistribution hm u)) = _
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    (hasTemperateGrowth_inverseShellDensity hm) (hasTemperateGrowth_complexShellDensity hm)]
  have hprod : inverseShellDensity m * complexShellDensity m = fun _ => 1 := by
    funext p
    exact inverseShellDensity_mul_density hm p
  rw [hprod, TemperedDistribution.smulLeftCLM_const, one_smul]

theorem unweightedMomentumDistribution_injective {m : ℝ} (hm : 0 < m) :
    Function.Injective (unweightedMomentumDistribution hm) := by
  intro u v h
  apply physicalMomentumDistribution_injective hm
  rw [← reweight_unweightedMomentumDistribution hm u,
    ← reweight_unweightedMomentumDistribution hm v, h]

private theorem density_cancel_pairing {m : ℝ} (hm : 0 < m)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)
    (u : Lp ℂ 2 (oneParticleMeasure m)) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticleWeight m p •
      ((SchwartzMap.smulLeftCLM ℂ (inverseShellDensity m) φ) p * u p) = φ p * u p := by
  rw [SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_inverseShellDensity hm),
    NNReal.smul_def, Complex.real_smul, ← complexShellDensity_eq_weight hm]
  change complexShellDensity m p * ((inverseShellDensity m p * φ p) * u p) = _
  calc
    _ = (inverseShellDensity m p * complexShellDensity m p) * (φ p * u p) := by ring
    _ = _ := by rw [inverseShellDensity_mul_density hm, one_mul]

/-- Every Schwartz test has an absolutely integrable unweighted pairing with a
physical mass-shell `L²` vector. -/
theorem integrable_unweightedMomentum_pairing {m : ℝ} (hm : 0 < m)
    (u : Lp ℂ 2 (oneParticleMeasure m))
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    Integrable (fun p => φ p * u p) := by
  let := oneParticleMeasure_hasTemperateGrowth hm
  have h := ((SchwartzMap.smulLeftCLM ℂ (inverseShellDensity m) φ).memLp
    2 (oneParticleMeasure m)).integrable_mul (Lp.memLp u)
  change Integrable (fun p =>
    (SchwartzMap.smulLeftCLM ℂ (inverseShellDensity m) φ) p * u p)
    (oneParticleMeasure m) at h
  change Integrable (fun p =>
    (SchwartzMap.smulLeftCLM ℂ (inverseShellDensity m) φ) p * u p)
    (volume.withDensity (fun p => (oneParticleWeight m p : ENNReal))) at h
  rw [integrable_withDensity_iff_integrable_smul (measurable_oneParticleWeight hm)] at h
  simpa only [density_cancel_pairing hm φ u] using h

/-- The normalization is exactly the ordinary spatial volume pairing. -/
theorem unweightedMomentumDistribution_apply {m : ℝ} (hm : 0 < m)
    (u : Lp ℂ 2 (oneParticleMeasure m))
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) :
    unweightedMomentumDistribution hm u φ = ∫ p, φ p * u p := by
  change physicalMomentumDistribution hm u
    (SchwartzMap.smulLeftCLM ℂ (inverseShellDensity m) φ) = _
  rw [physicalMomentumDistribution_apply]
  change (∫ p, (SchwartzMap.smulLeftCLM ℂ (inverseShellDensity m) φ) p * u p
    ∂volume.withDensity (fun p => (oneParticleWeight m p : ENNReal))) = _
  rw [integral_withDensity_eq_integral_smul (measurable_oneParticleWeight hm)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (density_cancel_pairing hm φ u)

end VacuumBellSeparation
