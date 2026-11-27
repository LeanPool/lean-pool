/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianBargmannDiagonal
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeSandwichCoherentTrace

/-!
# Actual noncommuting Gaussian sandwich existence and determinant trace

The input Gaussian property is the actual Weyl characteristic. The derived
coherent diagonal is integrated before any extension exists. The resulting
weighted summability constructs the genuine positive trace-class inverse
sandwich and gives its determinant trace. Covariance gap positivity is the
proved finite-matrix criterion, rather than an assumed operator theorem.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix MeasureTheory
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

/-- Gaussian thermal trace factor. -/
def gaussianThermalTraceFactor (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) : ℝ :=
  (∏ j, (1 - q j)) ^ (-τ) /
    (Real.sqrt (V + (1 / 2 : ℝ) • 1).det * Real.sqrt (thermalCoherentPrecision q τ V).det)

theorem gaussianThermalSandwich_coherent_diagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) (z : Fin m → ℂ) :
    multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z =
      ((Real.pi ^ m)⁻¹ * (∏ j, (1 - q j)) ^ (-τ) *
        (Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹) *
          coherentMatrixGaussian (thermalCoherentPrecision q τ V) z := by
  have h := multiThermalSandwichForm_coherent_diagonal hq₀ hq₁ hτ A
    (WithLp.toLp 2 z)
  simp only [] at h
  rw [gaussianPhysical_bargmann_diagonal hA hG hC] at h
  have he : Complex.exp ((-‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 : ℝ) : ℂ) *
      (((∏ j, (1 - q j)) ^ (-τ) : ℝ) : ℂ) *
      (((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ) *
        Complex.exp (((‖(WithLp.toLp 2 (multiModeInversePowerLabel q (τ / 2) z) :
            MultiModePhaseSpace m)‖ ^ 2 -
          complexRealCoordinates m (multiModeInversePowerLabel q (τ / 2) z) ⬝ᵥ
            ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ
              complexRealCoordinates m (multiModeInversePowerLabel q (τ / 2) z))) : ℝ) : ℂ)) =
      (((∏ j, (1 - q j)) ^ (-τ) * (Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℝ) : ℂ) *
        Complex.exp ((-(complexRealCoordinates m z ⬝ᵥ
          (thermalCoherentPrecision q τ V *ᵥ complexRealCoordinates m z)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    calc
      _ = ((((∏ j, (1 - q j)) ^ (-τ) : ℝ) : ℂ) *
          ((Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹ : ℂ)) *
          (Complex.exp ((-‖(WithLp.toLp 2 z : MultiModePhaseSpace m)‖ ^ 2 : ℝ) : ℂ) *
            Complex.exp (((‖(WithLp.toLp 2 (multiModeInversePowerLabel q (τ / 2) z) :
                MultiModePhaseSpace m)‖ ^ 2 -
              complexRealCoordinates m (multiModeInversePowerLabel q (τ / 2) z) ⬝ᵥ
                ((V + (1 / 2 : ℝ) • 1)⁻¹ *ᵥ
                  complexRealCoordinates m (multiModeInversePowerLabel q
                    (τ / 2) z))) : ℝ) : ℂ)) := by ring
      _ = _ := by
        rw [← Complex.exp_add, ← Complex.ofReal_add, thermalCoherentPrecision_coherent_exponent]
        simp only [Complex.ofReal_inv]
  rw [he] at h
  rw [multiThermalSandwichCoherentDiagonal, h]
  simp only [← Complex.ofReal_exp, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, coherentMatrixGaussian]
  ring

theorem integrable_gaussianThermalSandwich_coherent_diagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    Integrable (multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A) := by
  have heq : multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A =
      fun z => ((Real.pi ^ m)⁻¹ * (∏ j, (1 - q j)) ^ (-τ) *
        (Real.sqrt (V + (1 / 2 : ℝ) • 1).det)⁻¹) *
          coherentMatrixGaussian (thermalCoherentPrecision q τ V) z :=
    funext (gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC)
  rw [heq]
  exact (integrable_coherentMatrixGaussian
    ((thermalCoherentPrecision_posDef_iff hq₀ hq₁ hτ V hC).mpr hgap)).const_mul _

theorem integral_gaussianThermalSandwich_coherent_diagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    (∫ z : Fin m → ℂ, multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z) =
      gaussianThermalTraceFactor q τ V := by
  have hP := (thermalCoherentPrecision_posDef_iff hq₀ hq₁ hτ V hC).mpr hgap
  simp_rw [gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC]
  rw [integral_const_mul, integral_coherentMatrixGaussian hP, gaussianThermalTraceFactor]
  field_simp [show Real.pi ^ m ≠ 0 by positivity,
    ne_of_gt (Real.sqrt_pos.mpr hC.det_pos), ne_of_gt (Real.sqrt_pos.mpr hP.det_pos)]

theorem lintegral_gaussianThermalSandwich_coherent_diagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    (∫⁻ z : Fin m → ℂ, ENNReal.ofReal (multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z)) =
      ENNReal.ofReal (gaussianThermalTraceFactor q τ V) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC hgap)
    (Filter.Eventually.of_forall (multiThermalSandwichCoherentDiagonal_nonneg hq₀ hq₁ hτ hA.1)),
    integral_gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC hgap]

theorem summable_gaussianInverseThermalDiagonal
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    Summable (multiInverseThermalDiagonal q τ A) := by
  apply (lintegral_multiThermalSandwichCoherentDiagonal_lt_top_iff hq₀ hq₁ hτ hA.1).mp
  rw [lintegral_gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC hgap]
  exact ENNReal.ofReal_lt_top

/-- Actual positive trace-class extension and determinant trace under the
source covariance gap, derived from the genuine Gaussian characteristic. -/
theorem exists_gaussian_positiveTraceClass_sandwich
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    ∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (τ / 2)) * Θ *
        (multiModeThermalDensity q ^ (τ / 2)) = A ∧
      positiveTrace Θ = ENNReal.ofReal (gaussianThermalTraceFactor q τ V) := by
  let hs := summable_gaussianInverseThermalDiagonal hq₀ hq₁ hτ hA hG hC hgap
  refine ⟨multiThermalSandwichOperator hq₀ hq₁ hA.1 hs,
    multiThermalSandwichOperator_isPositiveTraceClass hq₀ hq₁ hA.1 hs,
    multiThermalSandwichOperator_factorization hq₀ hq₁ hτ hA.1 hs, ?_⟩
  rw [positiveTrace_multiThermalSandwichOperator,
    ENNReal.ofReal_tsum_of_nonneg (multiInverseThermalDiagonal_nonneg hq₀ hq₁ τ hA.1) hs,
    ← lintegral_multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ hA.1]
  exact lintegral_gaussianThermalSandwich_coherent_diagonal hq₀ hq₁ hτ hA hG hC hgap

end VacuumBellSeparation.Gaussian
