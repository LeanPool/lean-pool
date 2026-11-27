/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianRelativePerturbationDefs
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSandwichTraceRatio

/-!
# Actual Appendix A sandwich identities in faithful thermal coordinates

The relative perturbation is literally H^(-1/2)(Vρ-Vσ)H^(-1/2), with
H positive definite. Matrix factorization gives the normalized determinant
and its positive domain. The source trace and covariance identities are
then bundled for the actual positive trace-class inverse-domain extension.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem gaussianRelativePerturbation_factorization
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V =
      CFC.sqrt (thermalReferenceGap q τ) * (1 - gaussianRelativePerturbation q τ V) *
        CFC.sqrt (thermalReferenceGap q τ) := by
  have hH := thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁
  have hR := matrix_sqrt_posDef hH
  have hRR : CFC.sqrt (thermalReferenceGap q τ) * CFC.sqrt (thermalReferenceGap q τ) =
      thermalReferenceGap q τ := by
    simpa only [pow_two] using CFC.sq_sqrt (thermalReferenceGap q τ) hH.posSemidef.nonneg
  have h := perturbation_factorization (CFC.sqrt (thermalReferenceGap q τ))
    (V - thermalReferenceCovariance q) hR.isUnit
  rw [hRR] at h
  change thermalReferenceGap q τ - (V - thermalReferenceCovariance q) =
    CFC.sqrt (thermalReferenceGap q τ) * (1 - gaussianRelativePerturbation q τ V) *
      CFC.sqrt (thermalReferenceGap q τ) at h
  have he : thermalReferenceGap q τ - (V - thermalReferenceCovariance q) =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V := by
    unfold thermalReferenceGap
    abel
  rwa [he] at h

theorem one_sub_gaussianRelativePerturbation_posDef
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    (1 - gaussianRelativePerturbation q τ V).PosDef := by
  have hR := matrix_sqrt_posDef (thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁)
  have h := hR.isUnit.posDef_star_right_conjugate_iff
    (x := 1 - gaussianRelativePerturbation q τ V)
  simp only [Matrix.star_eq_conjTranspose, hR.isHermitian.eq] at h
  exact h.mp (by rwa [← gaussianRelativePerturbation_factorization hq₀ hq₁ hτ₀ hτ₁])

theorem gaussianRelativePerturbation_det_ratio
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (thermalReferenceGap q τ).det /
      (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).det =
        1 / (1 - gaussianRelativePerturbation q τ V).det := by
  have hH := thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁
  have hR := matrix_sqrt_posDef hH
  have hRR : CFC.sqrt (thermalReferenceGap q τ) * CFC.sqrt (thermalReferenceGap q τ) =
      thermalReferenceGap q τ := by
    simpa only [pow_two] using CFC.sq_sqrt (thermalReferenceGap q τ) hH.posSemidef.nonneg
  have h := det_div_det_perturbation (CFC.sqrt (thermalReferenceGap q τ))
    (V - thermalReferenceCovariance q) hR.isUnit
  rw [hRR] at h
  have he : thermalReferenceGap q τ - (V - thermalReferenceCovariance q) =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V := by
    unfold thermalReferenceGap
    abel
  rwa [he] at h

theorem positiveTrace_gaussian_factorization_appendixA
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    {A Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) :
    (positiveTrace Θ).toReal =
      (positiveTrace (multiModeThermalDensity q ^ (1 - τ))).toReal /
        Real.sqrt (1 - gaussianRelativePerturbation q τ V).det := by
  rw [positiveTrace_gaussian_factorization_appendixA_ratio hq₀ hq₁ hτ₀ hτ₁ hA hG hC hgap hΘ,
    gaussianRelativePerturbation_det_ratio hq₀ hq₁ hτ₀ hτ₁,
    Real.sqrt_div zero_le_one, Real.sqrt_one]
  ring

/-- The actual source sandwich in faithful thermal coordinates, with
its normalized Gaussian covariance and determinant trace. All operator
existence and Gaussianity have been derived from the actual characteristic. -/
theorem gaussian_sandwich_appendixA
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (τ / 2)) * Θ *
        (multiModeThermalDensity q ^ (τ / 2)) = A ∧
      positiveTrace (normalizedPositiveDensity Θ) = 1 ∧
      HasGaussianPhysicalCharacteristic (normalizedPositiveDensity Θ)
        (-modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) +
          CFC.sqrt (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) ^ 2 -
            (1 / 4 : ℝ) • 1) *
            (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V)⁻¹ *
          CFC.sqrt (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) ^ 2 -
            (1 / 4 : ℝ) • 1)) ∧
      (positiveTrace Θ).toReal =
        (positiveTrace (multiModeThermalDensity q ^ (1 - τ))).toReal /
          Real.sqrt (1 - gaussianRelativePerturbation q τ V).det := by
  obtain ⟨Θ, hΘtc, hΘ, ht, hn, hchar⟩ :=
    exists_gaussian_sandwich_with_normalized_covariance hq₀ hq₁ hτ₀ hA hG hC hgap
  refine ⟨Θ, hΘtc, hΘ, hn, ?_, ?_⟩
  · rwa [gaussianThermalCovariance_appendixA hq₀ hq₁ hτ₀ hC hgap] at hchar
  · exact positiveTrace_gaussian_factorization_appendixA hq₀ hq₁ hτ₀ hτ₁ hA hG hC hgap hΘ

end VacuumBellSeparation.Gaussian
