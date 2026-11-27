/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalWoodburyCovariance
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalDensityCharacteristic

/-!
# Appendix A trace calibrated by the actual thermal reference

Determinant factorization isolates the covariance gap. The remaining
constant is evaluated at the actual reference density, where the actual
CFC-power factorization has already been proved. Thus the final ratio
uses the actual positive trace of σ^(1-τ), not a formal calibration value.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {V W : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem thermalCoherentPrecision_det_product
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) :
    (V + (1 / 2 : ℝ) • 1).det * (thermalCoherentPrecision q τ V).det =
      (thermalDilationExcess q τ).det *
        (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).det := by
  let S := thermalDilationExcess q τ
  let T := thermalQuadratureDilation q τ
  let C := V + (1 / 2 : ℝ) • 1
  have hS := (thermalDilationExcess_posDef hq₀ hq₁ hτ).isUnit
  have hT := (thermalQuadratureDilation_posDef hq₀ τ).isUnit
  have hP : thermalCoherentPrecision q τ V = sandwichPrecision S T C := by
    dsimp only [S, T, C]
    rw [thermalCoherentPrecision, sandwichPrecision, ← thermalQuadratureDilation_sq hq₀]
    abel
  have hG : sandwichGap S T C =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V := by
    dsimp only [S, T, C]
    rw [sandwichGap, thermalDilationExcess_inverse_congruence hq₀ hq₁ hτ]
    abel
  have h := congrArg Matrix.det (sandwichPrecision_factorization S T C hS hT hC.isUnit)
  rw [← hP, hG] at h
  simp only [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv] at h
  change C.det * (thermalCoherentPrecision q τ V).det = S.det * _
  rw [h]
  have hCd : C.det ≠ 0 := hC.det_pos.ne'
  have hTd : T.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det T).mp hT).ne_zero
  field_simp [hTd, hCd]

theorem gaussianThermalTraceFactor_gap
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) :
    gaussianThermalTraceFactor q τ V =
      (∏ j, (1 - q j)) ^ (-τ) /
        (Real.sqrt (thermalDilationExcess q τ).det *
          Real.sqrt (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).det) := by
  rw [gaussianThermalTraceFactor, ← Real.sqrt_mul hC.det_pos.le,
    thermalCoherentPrecision_det_product hq₀ hq₁ hτ hC,
    Real.sqrt_mul (thermalDilationExcess_posDef hq₀ hq₁ hτ).det_pos.le]

theorem gaussianThermalTraceFactor_ratio
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hD : (W + (1 / 2 : ℝ) • 1).PosDef)
    (hgapV : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hgapW : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - W).PosDef) :
    gaussianThermalTraceFactor q τ V = gaussianThermalTraceFactor q τ W *
      Real.sqrt ((modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - W).det /
        (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).det) := by
  rw [gaussianThermalTraceFactor_gap hq₀ hq₁ hτ hC,
    gaussianThermalTraceFactor_gap hq₀ hq₁ hτ hD,
    Real.sqrt_div hgapW.det_pos.le]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (thermalDilationExcess_posDef hq₀ hq₁ hτ).det_pos),
    ne_of_gt (Real.sqrt_pos.mpr hgapV.det_pos), ne_of_gt (Real.sqrt_pos.mpr hgapW.det_pos)]

/-- Covariance of the product thermal reference with one occupation parameter per mode. -/
def thermalReferenceCovariance (q : Fin m → ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  modeDiagonal (fun j => thermalQuadratureVariance (q j))

/-- Thermal reference gap defined as `modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) -
thermalReferenceCovariance q`. -/
def thermalReferenceGap (q : Fin m → ℝ) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - thermalReferenceCovariance q

theorem thermalReferenceCovariance_add_half_posDef
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    (thermalReferenceCovariance q + (1 / 2 : ℝ) • 1).PosDef := by
  change (Matrix.diagonal (fun i : Fin m × Fin 2 => thermalQuadratureVariance (q i.1)) + _).PosDef
  rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_add]
  apply Matrix.PosDef.diagonal
  intro i
  have hv : 0 < thermalQuadratureVariance (q i.1) := by
    unfold thermalQuadratureVariance
    exact div_pos (by linarith [hq₀ i.1]) (mul_pos (by norm_num) (sub_pos.mpr (hq₁ i.1)))
  linarith

theorem thermalReferenceGap_posDef
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (thermalReferenceGap q τ).PosDef := by
  change (Matrix.diagonal (fun i : Fin m × Fin 2 => thermalQuadratureVariance (q i.1 ^ τ)) -
    Matrix.diagonal (fun i : Fin m × Fin 2 => thermalQuadratureVariance (q i.1))).PosDef
  rw [Matrix.diagonal_sub]
  apply Matrix.PosDef.diagonal
  intro i
  exact sub_pos.mpr ((thermalQuadratureVariance_lt_iff (hq₁ i.1)
    (Real.rpow_lt_one (hq₀ i.1).le (hq₁ i.1) hτ₀)).mpr
      (thermal_parameter_lt_rpow (hq₀ i.1) (hq₁ i.1) hτ₁))

theorem gaussianThermalTraceFactor_reference
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    gaussianThermalTraceFactor q τ (thermalReferenceCovariance q) =
      (positiveTrace (multiModeThermalDensity q ^ (1 - τ))).toReal := by
  have hA : IsPositiveTraceClass (multiModeThermalDensity q) := by
    refine ⟨multiModeThermalDensity_nonneg (fun j => (hq₀ j).le) hq₁, ?_⟩
    rw [positiveTrace_multiModeThermalDensity (fun j => (hq₀ j).le) hq₁]
    exact ENNReal.one_lt_top
  have hC := thermalReferenceCovariance_add_half_posDef (fun j => (hq₀ j).le) hq₁
  have hg := thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁
  have h := positiveTrace_gaussian_factorization hq₀ hq₁ hτ₀ hA
    (multiModeThermalDensity_hasGaussianPhysicalCharacteristic (fun j => (hq₀ j).le) hq₁)
    hC hg (multiModeThermalDensity_reference_factorization hq₀ hq₁ hτ₀ hτ₁)
  have hr := congrArg ENNReal.toReal h
  change (positiveTrace (multiModeThermalDensity q ^ (1 - τ))).toReal =
    (ENNReal.ofReal (gaussianThermalTraceFactor q τ (thermalReferenceCovariance q))).toReal at hr
  rw [ENNReal.toReal_ofReal (gaussianThermalTraceFactor_pos hq₀ hq₁ hτ₀ hC hg).le] at hr
  exact hr.symm

/-- The source determinant-ratio trace formula for the actual inverse
sandwich, calibrated against the actual CFC power of the reference density. -/
theorem positiveTrace_gaussian_factorization_appendixA_ratio
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    {A Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hG : HasGaussianPhysicalCharacteristic A V)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef)
    (hΘ : (multiModeThermalDensity q ^ (τ / 2)) * Θ *
      (multiModeThermalDensity q ^ (τ / 2)) = A) :
    (positiveTrace Θ).toReal =
      (positiveTrace (multiModeThermalDensity q ^ (1 - τ))).toReal *
        Real.sqrt ((thermalReferenceGap q τ).det /
          (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).det) := by
  rw [positiveTrace_gaussian_factorization hq₀ hq₁ hτ₀ hA hG hC hgap hΘ,
    ENNReal.toReal_ofReal (gaussianThermalTraceFactor_pos hq₀ hq₁ hτ₀ hC hgap).le,
    gaussianThermalTraceFactor_ratio hq₀ hq₁ hτ₀ hC
      (thermalReferenceCovariance_add_half_posDef (fun j => (hq₀ j).le) hq₁)
      hgap (thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁),
    gaussianThermalTraceFactor_reference hq₀ hq₁ hτ₀ hτ₁]
  rfl

end VacuumBellSeparation.Gaussian
