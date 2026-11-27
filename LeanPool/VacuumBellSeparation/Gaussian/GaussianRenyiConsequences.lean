/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiExponentDefs
public import LeanPool.VacuumBellSeparation.Gaussian.IntrinsicGaussianRenyiBound
public import LeanPool.VacuumBellSeparation.Gaussian.FaithfulRenyiEffectBound
public import LeanPool.VacuumBellSeparation.Gaussian.SemidefiniteRenyiComparison

/-!
# Actual Gaussian exponential Rényi, effect and trace-distance bounds

The proved finite positive Gaussian quantity permits honest exponentiation
of its logarithmic estimate. The genuine full-Hilbert-space effect and
interpolation theorems then give the source consequences. The covariance
perturbation is still the literal normalized-power covariance difference.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped ENNReal Matrix.Norms.L2Operator

variable {m : ℕ}
  {ρ σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
  {Vρ Vσ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem faithful_gaussian_renyi_exp_bound
    (hρ : IsFaithfulDensity ρ) (hσ : IsFaithfulDensity σ)
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    {r : ℝ} (hr : 1 < r)
    (hsmall : ‖intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau r)‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹) :
    sandwichedRenyiQuantity ρ σ r ≤ ENNReal.ofReal (Real.exp (gaussianRenyiExponent ρ σ r)) := by
  obtain ⟨hQ0, hQt, hlog⟩ := faithful_gaussian_renyi_bound hρ hσ hVρ hVσ hGρ hGσ hr hsmall
  have hreal : 0 < (sandwichedRenyiQuantity ρ σ r).toReal :=
    ENNReal.toReal_pos hQ0.ne' hQt.ne
  have he := ENNReal.ofReal_le_ofReal ((Real.log_le_iff_le_exp hreal).mp hlog)
  simpa only [ENNReal.ofReal_toReal hQt.ne, gaussianRenyiExponent] using he

theorem faithful_gaussian_density_effect_bound
    (hρ : IsFaithfulDensity ρ) (hσ : IsFaithfulDensity σ)
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    {r : ℝ} (hr : 1 < r)
    (hsmall : ‖intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau r)‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹)
    {M : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hM0 : 0 ≤ M) (hM1 : M ≤ 1) :
    ENNReal.ofReal (densityExpectation (multiModeNumberBasis m) ρ M).re ^ r ≤
      ENNReal.ofReal (Real.exp (gaussianRenyiExponent ρ σ r)) *
        ENNReal.ofReal (densityExpectation (multiModeNumberBasis m) σ M).re ^ (r - 1) := by
  exact (faithful_sandwichedRenyi_density_effect_bound (multiModeNumberBasis m)
    hρ.isPositiveTraceClass hσ hr hM0 hM1).trans (_root_.mul_le_mul_left
      (faithful_gaussian_renyi_exp_bound hρ hσ hVρ hVσ hGρ hGσ hr hsmall) _)

theorem faithful_gaussian_trace_distance_bound
    (hρ : IsFaithfulDensity ρ) (hσ : IsFaithfulDensity σ)
    (hVρ : Vρ.IsHermitian) (hVσ : Vσ.IsHermitian)
    (hGρ : HasGaussianPhysicalCharacteristic ρ Vρ)
    (hGσ : HasGaussianPhysicalCharacteristic σ Vσ)
    {r : ℝ} (hr : 2 ≤ r)
    (hsmall : ‖intrinsicGaussianRelativePerturbation ρ σ (gaussianRenyiTau r)‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹) :
    operatorTraceNorm (ρ - σ) ≤
      (ENNReal.ofReal (Real.exp (gaussianRenyiExponent ρ σ r)) ^ (1 / (r - 1)) - 1) ^
        (1 / 2 : ℝ) := by
  have hr1 : 1 < r := lt_of_lt_of_le (by norm_num) hr
  exact (renyi_trace_distance hρ.1 hρ.2.1 hσ hr).trans (ENNReal.rpow_le_rpow
    (tsub_le_tsub_right (ENNReal.rpow_le_rpow
      (faithful_gaussian_renyi_exp_bound hρ hσ hVρ hVσ hGρ hGσ hr1 hsmall)
      (one_div_nonneg.mpr (sub_pos.mpr hr1).le)) 1) (by norm_num))

end VacuumBellSeparation.Gaussian
