/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianSandwichNormalization

/-!
# Literal Appendix A covariance of the actual normalized sandwich

The thermal mode identities identify the positive Woodbury factor with
the actual matrix CFC square root. The already proved noncommuting inverse
identity then rewrites the actual normalized covariance in the manuscript's
form. Every inverse is justified by a positive-definite matrix hypothesis.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
variable {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}

theorem modeDiagonal_sub_scalar (d : Fin m → ℝ) (c : ℝ) :
    modeDiagonal (fun j => d j - c) = modeDiagonal d - c • 1 := by
  simp only [modeDiagonal, Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]

theorem thermal_scalar_excess_inverse {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    (q ^ (-τ) - 1)⁻¹ = thermalQuadratureVariance (q ^ τ) - 1 / 2 := by
  have ht₀ := Real.rpow_pos_of_pos hq₀ τ
  have ht₁ := Real.rpow_lt_one hq₀.le hq₁ hτ
  have hden : (q ^ τ)⁻¹ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ((one_lt_inv₀ ht₀).mpr ht₁))
  rw [Real.rpow_neg hq₀.le, thermalQuadratureVariance]
  field_simp [ht₀.ne', hden, ne_of_gt (sub_pos.mpr ht₁)]
  ring

theorem thermalDilationExcess_inv
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    (thermalDilationExcess q τ)⁻¹ =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - (1 / 2 : ℝ) • 1 := by
  have hs (j : Fin m) : q j ^ (-τ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hq₀ j) (hq₁ j) (neg_neg_of_pos hτ)))
  rw [thermalDilationExcess, modeDiagonal_inv hs]
  simp_rw [thermal_scalar_excess_inverse (hq₀ _) (hq₁ _) hτ]
  exact modeDiagonal_sub_scalar _ _

/-- Thermal woodbury factor given by `modeDiagonal (fun j => q j ^ (-(τ / 2)) * (q j ^ (-τ) -
1)⁻¹)`. -/
def thermalWoodburyFactor (q : Fin m → ℝ) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  modeDiagonal (fun j => q j ^ (-(τ / 2)) * (q j ^ (-τ) - 1)⁻¹)

theorem thermalWoodburyFactor_posDef
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    (thermalWoodburyFactor q τ).PosDef :=
  modeDiagonal_posDef fun j => mul_pos (Real.rpow_pos_of_pos (hq₀ j) _)
    (inv_pos.mpr (sub_pos.mpr
      (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hq₀ j) (hq₁ j) (neg_neg_of_pos hτ))))

theorem thermalWoodburyFactor_eq_mul_inverse
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    thermalWoodburyFactor q τ =
      thermalQuadratureDilation q τ * (thermalDilationExcess q τ)⁻¹ := by
  have hs (j : Fin m) : q j ^ (-τ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hq₀ j) (hq₁ j) (neg_neg_of_pos hτ)))
  rw [thermalDilationExcess, modeDiagonal_inv hs, thermalQuadratureDilation, modeDiagonal_mul]
  rfl

theorem thermalWoodburyFactor_eq_inverse_mul
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    thermalWoodburyFactor q τ =
      (thermalDilationExcess q τ)⁻¹ * thermalQuadratureDilation q τ := by
  have hs (j : Fin m) : q j ^ (-τ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hq₀ j) (hq₁ j) (neg_neg_of_pos hτ)))
  rw [thermalDilationExcess, modeDiagonal_inv hs, thermalQuadratureDilation,
    modeDiagonal_mul, thermalWoodburyFactor]
  congr 1
  funext j
  ring

theorem thermalWoodburyFactor_sq
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    thermalWoodburyFactor q τ * thermalWoodburyFactor q τ =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) ^ 2 - (1 / 4 : ℝ) • 1 := by
  rw [thermalWoodburyFactor, modeDiagonal_mul, pow_two, modeDiagonal_mul,
    ← modeDiagonal_sub_scalar]
  congr 1
  funext j
  have h := thermal_scalar_dilation_threshold (hq₀ j) (hq₁ j) hτ
  have hi := thermal_scalar_excess_inverse (hq₀ j) (hq₁ j) hτ
  calc
    _ = (q j ^ (-(τ / 2)) * (q j ^ (-τ) - 1)⁻¹ * q j ^ (-(τ / 2))) *
        (q j ^ (-τ) - 1)⁻¹ := by ring
    _ = _ := by rw [h, hi]; ring

/-- The Woodbury factor is the genuine positive CFC square root used in
Appendix A, including its strict positivity for faithful thermal modes. -/
theorem thermalWoodburyFactor_eq_sqrt
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    thermalWoodburyFactor q τ =
      CFC.sqrt (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) ^ 2 -
        (1 / 4 : ℝ) • 1) :=
  (CFC.sqrt_unique (thermalWoodburyFactor_sq hq₀ hq₁ hτ)
    (thermalWoodburyFactor_posDef hq₀ hq₁ hτ).posSemidef.nonneg).symm

theorem gaussianThermalCovariance_woodbury
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    gaussianThermalCovariance q τ V =
      -modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) +
        thermalWoodburyFactor q τ *
          (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V)⁻¹ *
            thermalWoodburyFactor q τ := by
  let S := thermalDilationExcess q τ
  let T := thermalQuadratureDilation q τ
  let C := V + (1 / 2 : ℝ) • 1
  have hP : thermalCoherentPrecision q τ V = sandwichPrecision S T C := by
    dsimp only [S, T, C]
    rw [thermalCoherentPrecision, sandwichPrecision, ← thermalQuadratureDilation_sq hq₀]
    abel
  have hG : sandwichGap S T C =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V := by
    dsimp only [S, T, C]
    rw [sandwichGap, thermalDilationExcess_inverse_congruence hq₀ hq₁ hτ]
    abel
  have hGi : IsUnit (sandwichGap S T C) := hG.symm ▸ hgap.isUnit
  have h := sandwichPrecision_inv S T C
    (thermalDilationExcess_posDef hq₀ hq₁ hτ).isUnit
    (thermalQuadratureDilation_posDef hq₀ τ).isUnit hC.isUnit hGi
  rw [← hP, hG] at h
  have hL := thermalWoodburyFactor_eq_mul_inverse hq₀ hq₁ hτ
  have hL' := thermalWoodburyFactor_eq_inverse_mul hq₀ hq₁ hτ
  have hprod : S⁻¹ * T *
      (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V)⁻¹ * T * S⁻¹ =
      thermalWoodburyFactor q τ *
        (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V)⁻¹ *
          thermalWoodburyFactor q τ := by
    calc
      _ = (S⁻¹ * T) *
          (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V)⁻¹ *
            (T * S⁻¹) := by noncomm_ring
      _ = _ := by rw [← hL, ← hL']
  rw [gaussianThermalCovariance, h, hprod]
  change -(thermalDilationExcess q τ)⁻¹ + _ - (1 / 2 : ℝ) • 1 = _
  rw [thermalDilationExcess_inv hq₀ hq₁ hτ]
  abel

/-- Appendix A covariance formula with the literal actual positive square root. -/
theorem gaussianThermalCovariance_appendixA
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef)
    (hgap : (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V).PosDef) :
    gaussianThermalCovariance q τ V =
      -modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) +
        CFC.sqrt (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) ^ 2 -
          (1 / 4 : ℝ) • 1) *
          (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) - V)⁻¹ *
        CFC.sqrt (modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ)) ^ 2 -
          (1 / 4 : ℝ) • 1) := by
  rw [gaussianThermalCovariance_woodbury hq₀ hq₁ hτ hC hgap,
    thermalWoodburyFactor_eq_sqrt hq₀ hq₁ hτ]

end VacuumBellSeparation.Gaussian
