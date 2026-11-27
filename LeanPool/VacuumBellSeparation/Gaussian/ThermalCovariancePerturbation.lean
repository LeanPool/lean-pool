/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPerturbationMultiplier

/-!
# The manuscript's thermal covariance perturbation estimates

The covariance is the actual Appendix A inverse sandwich expression.
Its value at the reference covariance is derived mode by mode. The two
norm estimates then follow from the genuine matrix resolvent estimates,
without a commutativity assumption on the input perturbation.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

/-- Thermal sandwich covariance. -/
def thermalSandwichCovariance (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  -thermalPowerCovariance q τ + thermalWoodburyFactor q τ *
    (thermalPowerCovariance q τ - V)⁻¹ * thermalWoodburyFactor q τ

/-- Thermal sandwich relative perturbation. -/
def thermalSandwichRelativePerturbation (q : Fin m → ℝ) (τ : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  relativeCovariancePerturbation (thermalPowerCovariance q (1 - τ))
    (thermalSandwichCovariance q τ V - thermalPowerCovariance q (1 - τ))

theorem gaussianRelativePerturbation_eq_relative :
    gaussianRelativePerturbation q τ V =
      relativeCovariancePerturbation (thermalReferenceGap q τ)
        (V - thermalReferenceCovariance q) := rfl

theorem thermalSandwichCovariance_reference
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    thermalSandwichCovariance q τ (thermalReferenceCovariance q) =
      thermalPowerCovariance q (1 - τ) := by
  have hH (j : Fin m) : 0 < thermalQuadratureVariance (q j ^ τ) -
      thermalQuadratureVariance (q j) :=
    sub_pos.mpr ((thermalQuadratureVariance_lt_iff (hq₁ j)
      (Real.rpow_lt_one (hq₀ j).le (hq₁ j) hτ₀)).mpr
        (thermal_parameter_lt_rpow (hq₀ j) (hq₁ j) hτ₁))
  have hgap : thermalPowerCovariance q τ - thermalReferenceCovariance q =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ) -
        thermalQuadratureVariance (q j)) := Matrix.diagonal_sub _ _
  have hL (j : Fin m) :
      (q j ^ (-(τ / 2)) * (q j ^ (-τ) - 1)⁻¹) ^ 2 =
        thermalQuadratureVariance (q j ^ τ) ^ 2 - 1 / 4 := by
    have h := thermal_scalar_dilation_threshold (hq₀ j) (hq₁ j) hτ₀
    have hi := thermal_scalar_excess_inverse (hq₀ j) (hq₁ j) hτ₀
    calc
      _ = (q j ^ (-(τ / 2)) * (q j ^ (-τ) - 1)⁻¹ * q j ^ (-(τ / 2))) *
          (q j ^ (-τ) - 1)⁻¹ := by ring
      _ = _ := by rw [h, hi]; ring
  rw [thermalSandwichCovariance, hgap, modeDiagonal_inv (fun j => (hH j).ne'),
    thermalWoodburyFactor, modeDiagonal_mul, modeDiagonal_mul]
  simp only [thermalPowerCovariance, modeDiagonal, Matrix.diagonal_neg, Matrix.diagonal_add]
  congr 1
  funext i
  have h := thermal_reference_scalar_identity (hq₀ i.1) (hq₁ i.1) hτ₀ hτ₁
  have he :
      (q i.1 ^ (-(τ / 2)) * (q i.1 ^ (-τ) - 1)⁻¹) *
        (thermalQuadratureVariance (q i.1 ^ τ) - thermalQuadratureVariance (q i.1))⁻¹ *
        (q i.1 ^ (-(τ / 2)) * (q i.1 ^ (-τ) - 1)⁻¹) =
      (thermalQuadratureVariance (q i.1 ^ τ) ^ 2 - 1 / 4) /
        (thermalQuadratureVariance (q i.1 ^ τ) - thermalQuadratureVariance (q i.1)) := by
    rw [← hL i.1]
    ring
  rw [he]
  linarith

theorem thermalSandwichCovariance_sub_reference
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    thermalSandwichCovariance q τ V - thermalPowerCovariance q (1 - τ) =
      inverseSandwichPerturbation (thermalReferenceGap q τ) (thermalWoodburyFactor q τ)
        (V - thermalReferenceCovariance q) := by
  rw [← thermalSandwichCovariance_reference hq₀ hq₁ hτ₀ hτ₁,
    thermalSandwichCovariance, thermalSandwichCovariance, inverseSandwichPerturbation]
  have hg : thermalReferenceGap q τ - (V - thermalReferenceCovariance q) =
      thermalPowerCovariance q τ - V := by
    unfold thermalReferenceGap thermalPowerCovariance
    abel
  rw [hg]
  change -thermalPowerCovariance q τ + _ - (-thermalPowerCovariance q τ + _) = _
  unfold thermalReferenceGap thermalPowerCovariance
  abel

theorem thermal_covariance_gap_posDef_of_relative_norm
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hV : V.IsHermitian) (hδ : ‖gaussianRelativePerturbation q τ V‖ < 1) :
    (thermalPowerCovariance q τ - V).PosDef := by
  have h₀ : (thermalReferenceCovariance q).IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have h := covariance_gap_posDef_of_relative_norm
    (thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁) (hV.sub h₀) hδ
  have hg : thermalReferenceGap q τ - (V - thermalReferenceCovariance q) =
      thermalPowerCovariance q τ - V := by
    unfold thermalReferenceGap thermalPowerCovariance
    abel
  rwa [hg] at h

theorem norm_thermalSandwichRelativePerturbation_le
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hV : V.IsHermitian) (hδ : ‖gaussianRelativePerturbation q τ V‖ < 1) :
    ‖thermalSandwichRelativePerturbation q τ V‖ ≤ thermalPerturbationConstant τ *
      (‖gaussianRelativePerturbation q τ V‖ / (1 - ‖gaussianRelativePerturbation q τ V‖)) := by
  have h₀ : (thermalReferenceCovariance q).IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have h := norm_relative_inverseSandwichPerturbation_le
    (thermalPowerCovariance_posDef (fun j => (hq₀ j).le) hq₁ (sub_pos.mpr hτ₁))
    (thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁)
    (thermalWoodburyFactor_posDef hq₀ hq₁ hτ₀).isHermitian (hV.sub h₀) hδ
  rw [thermalSandwichRelativePerturbation,
    thermalSandwichCovariance_sub_reference hq₀ hq₁ hτ₀ hτ₁]
  exact h.trans (mul_le_mul_of_nonneg_right
    (norm_sq_thermalPerturbationMultiplier_le hq₀ hq₁ hτ₀ hτ₁)
      (div_nonneg (norm_nonneg _) (sub_pos.mpr hδ).le))

theorem matrixTraceNorm_thermalSandwichRelativePerturbation_le
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1)
    (hV : V.IsHermitian) (hδ : ‖gaussianRelativePerturbation q τ V‖ < 1) :
    matrixTraceNorm (thermalSandwichRelativePerturbation q τ V) ≤
      thermalPerturbationConstant τ / (1 - ‖gaussianRelativePerturbation q τ V‖) *
        matrixTraceNorm (gaussianRelativePerturbation q τ V) := by
  have h₀ : (thermalReferenceCovariance q).IsHermitian := by
    exact Matrix.isHermitian_diagonal _
  have h := matrixTraceNorm_relative_inverseSandwichPerturbation_le
    (thermalPowerCovariance_posDef (fun j => (hq₀ j).le) hq₁ (sub_pos.mpr hτ₁))
    (thermalReferenceGap_posDef hq₀ hq₁ hτ₀ hτ₁)
    (thermalWoodburyFactor_posDef hq₀ hq₁ hτ₀).isHermitian (hV.sub h₀) hδ
  rw [thermalSandwichRelativePerturbation,
    thermalSandwichCovariance_sub_reference hq₀ hq₁ hτ₀ hτ₁]
  calc
    _ ≤ _ := h
    _ ≤ thermalPerturbationConstant τ *
        ((1 - ‖gaussianRelativePerturbation q τ V‖)⁻¹ *
          matrixTraceNorm (gaussianRelativePerturbation q τ V)) :=
      mul_le_mul_of_nonneg_right
        (norm_sq_thermalPerturbationMultiplier_le hq₀ hq₁ hτ₀ hτ₁)
        (mul_nonneg (inv_nonneg.mpr (sub_pos.mpr hδ).le) (matrixTraceNorm_nonneg _))
    _ = _ := by ring

end VacuumBellSeparation.Gaussian
