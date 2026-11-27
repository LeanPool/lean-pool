/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPurityPerturbation
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPartitionCancellation

/-!
# Actual Gaussian sandwich power trace and the Rényi bound

For the source relative-norm hypothesis, every actual solution of the
faithful thermal factorization is the unique positive trace-class inverse
sandwich. Its genuine r-th CFC power has strictly positive finite trace.
Partition cancellation and the aggregate purity estimate give the source
constant 2 r max(2,1/τ), with no commuting covariance assumption.

The theorem retains the actual input strict quantum condition explicitly.
It is stated for the bounded extension of the inverse-domain sandwich;
no totalized inverse of the faithful density is used.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ r : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
variable {A Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}

theorem gaussian_thermal_factorization_power_log
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (hτ₀ : 0 < τ) (hτ₁ : τ < 1) (hr : 1 < r) (hrτ : r * (1 - τ) = 1)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hV : V.IsHermitian) (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hδ : ‖gaussianRelativePerturbation q τ V‖ ≤
      (4 * thermalPerturbationConstant τ)⁻¹)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) :
    (0 < positiveTrace (Θ ^ r) ∧ positiveTrace (Θ ^ r) < ⊤) ∧
    Real.log (positiveTrace (Θ ^ r)).toReal =
      -(r / 2) * Real.log (1 - gaussianRelativePerturbation q τ V).det +
        covariancePurityTrace r (thermalSandwichCovariance q τ V) -
          covariancePurityTrace r (thermalPowerCovariance q (1 - τ)) := by
  have hb := thermal_smallness_norm_bounds hq₀ hq₁ hτ₀ hτ₁ hV hδ
  have hz : ‖gaussianRelativePerturbation q τ V‖ < 1 := by linarith [hb.1]
  have hgap := thermal_covariance_gap_posDef_of_relative_norm hq₀ hq₁ hτ₀ hτ₁ hV hz
  have hΘtc := gaussian_factorization_isPositiveTraceClass hq₀ hq₁ hτ₀ hA hG hC hgap hΘ
  have ht : 0 < positiveTrace Θ := by
    rw [positiveTrace_gaussian_factorization hq₀ hq₁ hτ₀ hA hG hC hgap hΘ]
    exact ENNReal.ofReal_pos.mpr (gaussianThermalTraceFactor_pos hq₀ hq₁ hτ₀ hC hgap)
  have hntc := normalizedPositiveDensity_isPositiveTraceClass (multiModeNumberBasis m) hΘtc
  have hK := thermalSandwichCovariance_posDef_of_small_relative_norm hq₀ hq₁ hτ₀ hτ₁ hV hδ
  have hQK := (thermalSandwichCovariance_quantum_posDef_iff hq₀ hq₁ hτ₀ hgap).mpr hQ
  have hGK : HasGaussianPhysicalCharacteristic (normalizedPositiveDensity Θ)
      (thermalSandwichCovariance q τ V) := by
    have h := normalized_gaussian_factorization_hasGaussianPhysicalCharacteristic
      hq₀ hq₁ hτ₀ hA hG hC hgap hΘ
    rwa [gaussianThermalCovariance_woodbury hq₀ hq₁ hτ₀ hC hgap] at h
  have hnr := gaussianPhysical_rpow_trace_pos_finite_of_strict_quantum hntc hK hQK hGK
    (by linarith : 0 < r)
  refine ⟨positiveDensity_rpow_trace_pos_finite_of_normalized (multiModeNumberBasis m)
    hΘtc ht (by linarith) hnr, ?_⟩
  have hnormalization : Real.log (positiveTrace (Θ ^ r)).toReal =
      r * Real.log (positiveTrace Θ).toReal +
        Real.log (positiveTrace (normalizedPositiveDensity Θ ^ r)).toReal :=
    log_positiveTrace_rpow_normalization (multiModeNumberBasis m) hΘtc ht
      (r := r) (by linarith) hnr
  have hpurity : Real.log (positiveTrace (normalizedPositiveDensity Θ ^ r)).toReal =
      covariancePurityTrace r (thermalSandwichCovariance q τ V) :=
    log_positiveTrace_gaussianPhysical_rpow_eq_purity hntc hK hQK hGK (r := r) (by linarith)
  rw [hnormalization, hpurity]
  have htrace := positiveTrace_gaussian_factorization_appendixA hq₀ hq₁ hτ₀ hτ₁ hA hG hC hgap hΘ
  have href := positiveTrace_multiModeThermalDensity_rpow_pos_finite
    (fun j => (hq₀ j).le) hq₁ (sub_pos.mpr hτ₁)
  have hrefR := ENNReal.toReal_pos href.1.ne' href.2.ne
  have hdet := (one_sub_gaussianRelativePerturbation_posDef hq₀ hq₁ hτ₀ hτ₁ hgap).det_pos
  have hpart := thermalPowerCovariance_partition_cancellation hq₀ hq₁ (sub_pos.mpr hτ₁)
    (by linarith : 0 < r) (by simpa only [mul_comm] using hrτ)
  rw [htrace, Real.log_div hrefR.ne' (Real.sqrt_pos.mpr hdet).ne', Real.log_sqrt hdet.le]
  nlinarith [hpart]

theorem gaussian_thermal_factorization_renyi_bound
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (hτ₀ : 0 < τ) (hτ₁ : τ < 1) (hr : 1 < r) (hrτ : r * (1 - τ) = 1)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hV : V.IsHermitian) (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hδ : ‖gaussianRelativePerturbation q τ V‖ ≤
      (4 * thermalPerturbationConstant τ)⁻¹)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) :
    Real.log (positiveTrace (Θ ^ r)).toReal ≤
      2 * r * thermalPerturbationConstant τ * matrixTraceNorm
        (gaussianRelativePerturbation q τ V) := by
  have hb := thermal_smallness_norm_bounds hq₀ hq₁ hτ₀ hτ₁ hV hδ
  have hz : ‖gaussianRelativePerturbation q τ V‖ < 1 := by linarith [hb.1]
  have hlog := abs_log_det_one_sub_le
    (gaussianRelativePerturbation_isHermitian hV hq₀ hq₁ hτ₀ hτ₁) hz
  have hp := thermalSandwichCovariance_purity_bound hq₀ hq₁ hτ₀ hτ₁ hr hV hQ hδ
  rw [(gaussian_thermal_factorization_power_log hq₀ hq₁ hτ₀ hτ₁ hr hrτ
    hA hG hV hC hQ hδ hΘ).2]
  calc
    _ ≤ (r / 2) * |Real.log (1 - gaussianRelativePerturbation q τ V).det| +
        |covariancePurityTrace r (thermalSandwichCovariance q τ V) -
          covariancePurityTrace r (thermalPowerCovariance q (1 - τ))| := by
      have := neg_le_abs (Real.log (1 - gaussianRelativePerturbation q τ V).det)
      have := le_abs_self (covariancePurityTrace r (thermalSandwichCovariance q τ V) -
        covariancePurityTrace r (thermalPowerCovariance q (1 - τ)))
      nlinarith
    _ ≤ (r / 2) * (matrixTraceNorm (gaussianRelativePerturbation q τ V) /
          (1 - ‖gaussianRelativePerturbation q τ V‖)) +
        (r / 2) * (thermalPerturbationConstant τ /
          ((1 - ‖gaussianRelativePerturbation q τ V‖) *
            (1 - ‖thermalSandwichRelativePerturbation q τ V‖))) *
              matrixTraceNorm (gaussianRelativePerturbation q τ V) :=
      add_le_add (mul_le_mul_of_nonneg_left hlog (by linarith)) hp
    _ = (r / 2) * ((1 - ‖gaussianRelativePerturbation q τ V‖)⁻¹ +
        thermalPerturbationConstant τ / ((1 - ‖gaussianRelativePerturbation q τ V‖) *
          (1 - ‖thermalSandwichRelativePerturbation q τ V‖))) *
            matrixTraceNorm (gaussianRelativePerturbation q τ V) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (renyi_final_numeric_bound (by linarith) (two_le_thermalPerturbationConstant τ) hb.1 hb.2)
      (matrixTraceNorm_nonneg _)

/-- Source-normalized order r and constant max(2,τ⁻¹), with an actual
positive trace-class inverse sandwich and a finite genuine power trace. -/
theorem exists_gaussian_thermal_renyi_bound
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hr : 1 < r)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hV : V.IsHermitian) (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hδ : ‖gaussianRelativePerturbation q (gaussianRenyiTau r) V‖ ≤
      (4 * max 2 (gaussianRenyiTau r)⁻¹)⁻¹) :
    ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (gaussianRenyiTau r / 2)) * Θ *
        (multiModeThermalDensity q ^ (gaussianRenyiTau r / 2)) = A ∧
      0 < positiveTrace (Θ ^ r) ∧ positiveTrace (Θ ^ r) < ⊤ ∧
      Real.log (positiveTrace (Θ ^ r)).toReal ≤
        2 * r * max 2 (gaussianRenyiTau r)⁻¹ *
          matrixTraceNorm (gaussianRelativePerturbation q (gaussianRenyiTau r) V) := by
  have hτ₀ := gaussianRenyiTau_pos hr
  have hτ₁ := gaussianRenyiTau_lt_one hr
  have hsmall : ‖gaussianRelativePerturbation q (gaussianRenyiTau r) V‖ ≤
      (4 * thermalPerturbationConstant (gaussianRenyiTau r))⁻¹ := by
    rwa [thermalPerturbationConstant_eq_max hτ₀]
  obtain ⟨Θ, hΘtc, hΘ, _⟩ := gaussian_sandwich_of_small_relative_norm
    hq₀ hq₁ hτ₀ hτ₁ hA hG hV hC hsmall
  have hp := (gaussian_thermal_factorization_power_log hq₀ hq₁ hτ₀ hτ₁ hr
    (mul_one_sub_gaussianRenyiTau hr) hA hG hV hC hQ hsmall hΘ).1
  refine ⟨Θ, hΘtc, hΘ, hp.1, hp.2, ?_⟩
  have hb := gaussian_thermal_factorization_renyi_bound hq₀ hq₁ hτ₀ hτ₁ hr
    (mul_one_sub_gaussianRenyiTau hr) hA hG hV hC hQ hsmall hΘ
  rwa [thermalPerturbationConstant_eq_max hτ₀] at hb

end VacuumBellSeparation.Gaussian
