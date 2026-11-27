/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRenyiParameters
public import LeanPool.VacuumBellSeparation.Gaussian.MatrixLogDetBound

/-!
# Actual Gaussian sandwiches under the manuscript's norm hypothesis

The norm hypothesis yields a genuine positive covariance gap, hence an
actual positive trace-class range-domain sandwich. Its normalized state
has the derived physical covariance, and that covariance satisfies both
perturbation bounds. The determinant logarithm is controlled separately.
No spectral purity differential or Rényi comparison is assumed or claimed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem gaussianRelativePerturbation_isHermitian (hV : V.IsHermitian)
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (gaussianRelativePerturbation q τ V).IsHermitian :=
  relativeCovariancePerturbation_isHermitian
    (thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁)
    (hV.sub (Matrix.isHermitian_diagonal _))

/-- The smallness hypothesis constructs an actual operator and identifies
its actual normalized physical covariance, with the source norm bounds. -/
theorem gaussian_sandwich_of_small_relative_norm
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hV : V.IsHermitian) (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hδ : ‖gaussianRelativePerturbation q τ V‖ ≤
      (4 * thermalPerturbationConstant τ)⁻¹) :
    ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (τ / 2)) * Θ *
        (multiModeThermalDensity q ^ (τ / 2)) = A ∧
      positiveTrace (normalizedPositiveDensity Θ) = 1 ∧
      HasGaussianPhysicalCharacteristic (normalizedPositiveDensity Θ)
        (thermalSandwichCovariance q τ V) ∧
      (positiveTrace Θ).toReal =
        (positiveTrace (multiModeThermalDensity q ^ (1 - τ))).toReal /
          Real.sqrt (1 - gaussianRelativePerturbation q τ V).det ∧
      ‖gaussianRelativePerturbation q τ V‖ ≤ 1 / 8 ∧
      ‖thermalSandwichRelativePerturbation q τ V‖ ≤ 2 / 7 ∧
      matrixTraceNorm (thermalSandwichRelativePerturbation q τ V) ≤
        thermalPerturbationConstant τ / (1 - ‖gaussianRelativePerturbation q τ V‖) *
          matrixTraceNorm (gaussianRelativePerturbation q τ V) ∧
      |(cfc Real.log (1 - gaussianRelativePerturbation q τ V)).trace| ≤
        matrixTraceNorm (gaussianRelativePerturbation q τ V) /
          (1 - ‖gaussianRelativePerturbation q τ V‖) := by
  have hb := thermal_smallness_norm_bounds hq₀ hq₁ hτ₀ hτ₁ hV hδ
  have hlt : ‖gaussianRelativePerturbation q τ V‖ < 1 := by linarith [hb.1]
  have hgap := thermal_covariance_gap_posDef_of_relative_norm hq₀ hq₁ hτ₀ hτ₁ hV hlt
  obtain ⟨Θ, hΘtc, hΘ, ht, hn, hchar⟩ :=
    exists_gaussian_sandwich_with_normalized_covariance hq₀ hq₁ hτ₀ hA hG hC hgap
  have hc : gaussianThermalCovariance q τ V = thermalSandwichCovariance q τ V :=
    gaussianThermalCovariance_woodbury hq₀ hq₁ hτ₀ hC hgap
  rw [hc] at hchar
  refine ⟨Θ, hΘtc, hΘ, hn, hchar, ?_, hb.1, hb.2, ?_, ?_⟩
  · exact positiveTrace_gaussian_factorization_appendixA hq₀ hq₁ hτ₀ hτ₁ hA hG hC hgap hΘ
  · exact matrixTraceNorm_thermalSandwichRelativePerturbation_le hq₀ hq₁ hτ₀ hτ₁ hV hlt
  · exact abs_trace_log_one_sub_le
      (gaussianRelativePerturbation_isHermitian hV hq₀ hq₁ hτ₀ hτ₁) hlt

end VacuumBellSeparation.Gaussian
