/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSandwichCriterion
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianDiagonalCharacteristic
public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTraceScaling

/-!
# Actual Gaussian covariance of the normalized inverse sandwich

Every bounded solution of the thermal factorization equals the constructed
range-domain extension. Its actual positive trace is the determinant
factor, strictly positive and finite under the covariance gap. Normalizing
the actual operator gives trace one and an actual Gaussian characteristic
with physical covariance `P⁻¹-I/2`, where P is the derived precision.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory ContinuousLinearMap
open scoped MatrixOrder Matrix.Norms.L2Operator

-- Prove the captured real-scalar normalization on an abstract Hilbert
-- carrier before specializing to the concrete multimode lp carrier.
private theorem re_inner_normalizedPositiveDensity
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (B : E →L[ℂ] E) (x : E) :
    (inner ℂ x (normalizedPositiveDensity B x)).re =
      (positiveTrace B).toReal⁻¹ * (inner ℂ x (B x)).re := by
  simp only [normalizedPositiveDensity, smul_apply,
    inner_smul_right_eq_smul, ← RCLike.re_eq_complex_re, RCLike.smul_re]

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {A Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

/-- Gaussian thermal covariance. -/
def gaussianThermalCovariance (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  (thermalCoherentPrecision q τ V)⁻¹ - (1 / 2 : ℝ) • 1

theorem gaussianThermalTraceFactor_pos
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    0 < gaussianThermalTraceFactor q τ V := by
  have hP := (thermalCoherentPrecision_posDef_iff hq₀ hq₁ hτ V hC).mpr hgap
  exact div_pos (Real.rpow_pos_of_pos
    (Finset.prod_pos fun j _ => sub_pos.mpr (hq₁ j)) _)
    (mul_pos (Real.sqrt_pos.mpr hC.det_pos) (Real.sqrt_pos.mpr hP.det_pos))

theorem gaussian_factorization_isPositiveTraceClass
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) : IsPositiveTraceClass Θ := by
  let hs := summable_gaussianInverseThermalDiagonal hq₀ hq₁ hτ hA hG hC hgap
  rw [multiThermalSandwichOperator_unique hq₀ hq₁ hτ hA.1 hs hΘ]
  exact multiThermalSandwichOperator_isPositiveTraceClass hq₀ hq₁ hA.1 hs

theorem positiveTrace_gaussian_factorization
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) :
    positiveTrace Θ = ENNReal.ofReal (gaussianThermalTraceFactor q τ V) := by
  let hs := summable_gaussianInverseThermalDiagonal hq₀ hq₁ hτ hA hG hC hgap
  rw [multiThermalSandwichOperator_unique hq₀ hq₁ hτ hA.1 hs hΘ,
    positiveTrace_multiThermalSandwichOperator,
    ENNReal.ofReal_tsum_of_nonneg (multiInverseThermalDiagonal_nonneg hq₀ hq₁ τ hA.1) hs,
    ← lintegral_multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ hA.1]
  exact lintegral_gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC hgap

theorem gaussian_factorization_coherentDiagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) (z : Fin m → ℂ) :
    multiCoherentPositiveDiagonal Θ z =
      ((Real.pi ^ m)⁻¹ * (∏ j, (1 - q j)) ^ (-τ) *
        (Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹) *
          coherentMatrixGaussian (thermalCoherentPrecision q τ V) z := by
  let hs := summable_gaussianInverseThermalDiagonal hq₀ hq₁ hτ hA hG hC hgap
  have heq := multiThermalSandwichOperator_unique hq₀ hq₁ hτ hA.1 hs hΘ
  have hform := multiThermalSandwichForm_eq_inner hq₀ hq₁ hτ hA.1 hs
    (multiDomainCoherentVector hq₀ hq₁ (half_pos hτ) (WithLp.toLp 2 z))
    (multiDomainCoherentVector hq₀ hq₁ (half_pos hτ) (WithLp.toLp 2 z))
  have hd : multiCoherentPositiveDiagonal Θ z =
      multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z := by
    rw [heq, multiCoherentPositiveDiagonal, multiThermalSandwichCoherentDiagonal, hform]
    rfl
  rw [hd]
  exact gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC z

theorem multiCoherentPositiveDiagonal_real_smul (c : ℝ)
    (B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (z : Fin m → ℂ) :
    multiCoherentPositiveDiagonal (c • B) z = c * multiCoherentPositiveDiagonal B z := by
  simp only [multiCoherentPositiveDiagonal, smul_apply,
    inner_smul_right_eq_smul,
    ← RCLike.re_eq_complex_re, RCLike.smul_re]
  ring

theorem normalized_gaussian_factorization_coherentDiagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) (z : Fin m → ℂ) :
    multiCoherentPositiveDiagonal (normalizedPositiveDensity Θ) z =
      (Real.sqrt (thermalCoherentPrecision q τ V).det / Real.pi ^ m) *
        coherentMatrixGaussian (thermalCoherentPrecision q τ V) z := by
  have hP := (thermalCoherentPrecision_posDef_iff hq₀ hq₁ hτ V hC).mpr hgap
  have ht := gaussianThermalTraceFactor_pos hq₀ hq₁ hτ hC hgap
  have hscale : multiCoherentPositiveDiagonal (normalizedPositiveDensity Θ) z =
      (positiveTrace Θ).toReal⁻¹ * multiCoherentPositiveDiagonal Θ z := by
    simp only [multiCoherentPositiveDiagonal, re_inner_normalizedPositiveDensity]
    ring
  rw [hscale, positiveTrace_gaussian_factorization hq₀ hq₁ hτ hA hG hC hgap hΘ,
    ENNReal.toReal_ofReal ht.le,
    gaussian_factorization_coherentDiagonal hq₀ hq₁ hτ hA hG hC hgap hΘ]
  rw [← mul_assoc]
  congr 1
  unfold gaussianThermalTraceFactor
  have hZ : 0 < (∏ j, (1 - q j)) ^ (-τ) := Real.rpow_pos_of_pos
    (Finset.prod_pos fun j _ => sub_pos.mpr (hq₁ j)) _
  field_simp [show Real.pi ^ m ≠ 0 by positivity, hZ.ne',
    ne_of_gt (Real.sqrt_pos.mpr hC.det_pos), ne_of_gt (Real.sqrt_pos.mpr hP.det_pos)]
  exact div_self (Real.sqrt_pos.mpr hC.det_pos).ne'

/-- Actual normalized operator Gaussianity, derived from its coherent
integral and actual Weyl expectation. The inverse precision is a genuine
matrix inverse because the strict source covariance gap implies PosDef. -/
theorem normalized_gaussian_factorization_hasGaussianPhysicalCharacteristic
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) :
    HasGaussianPhysicalCharacteristic (normalizedPositiveDensity Θ)
      (gaussianThermalCovariance q τ V) := by
  have hΘtc := gaussian_factorization_isPositiveTraceClass hq₀ hq₁ hτ hA hG hC hgap hΘ
  exact hasGaussianPhysicalCharacteristic_of_coherentDiagonal
    (normalizedPositiveDensity_isPositiveTraceClass (multiModeNumberBasis m) hΘtc)
    ((thermalCoherentPrecision_posDef_iff hq₀ hq₁ hτ V hC).mpr hgap)
    (normalized_gaussian_factorization_coherentDiagonal hq₀ hq₁ hτ hA hG hC hgap hΘ)

theorem exists_gaussian_sandwich_with_normalized_covariance
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (τ / 2)) * Θ *
        (multiModeThermalDensity q ^ (τ / 2)) = A ∧
      positiveTrace Θ = ENNReal.ofReal (gaussianThermalTraceFactor q τ V) ∧
      positiveTrace (normalizedPositiveDensity Θ) = 1 ∧
      HasGaussianPhysicalCharacteristic (normalizedPositiveDensity Θ)
        (gaussianThermalCovariance q τ V) := by
  obtain ⟨Θ, hΘtc, hΘ, ht⟩ :=
    exists_gaussian_positiveTraceClass_sandwich hq₀ hq₁ hτ hA hG hC hgap
  refine ⟨Θ, hΘtc, hΘ, ht, ?_, ?_⟩
  · apply positiveTrace_normalizedPositiveDensity (multiModeNumberBasis m) hΘtc
    rw [ht]
    exact ENNReal.ofReal_pos.mpr (gaussianThermalTraceFactor_pos hq₀ hq₁ hτ hC hgap)
  · exact normalized_gaussian_factorization_hasGaussianPhysicalCharacteristic
      hq₀ hq₁ hτ hA hG hC hgap hΘ

end VacuumBellSeparation.Gaussian
