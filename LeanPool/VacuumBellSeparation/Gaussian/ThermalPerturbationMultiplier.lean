/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CovarianceResolventPerturbation
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianAppendixA
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalVarianceComparison

/-!
# The actual thermal covariance perturbation multiplier

For τ in (0,1), the genuine multiplier T_(1-τ)^(-1/2) L H^(-1/2)
has squared operator norm at most 1+max{1,(1-τ)/τ}. The scalar thermal
identity and the actual diagonal square-root calculus prove this bound.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem modeDiagonal_sqrt {m : ℕ} {d : Fin m → ℝ} (hd : ∀ j, 0 ≤ d j) :
    CFC.sqrt (modeDiagonal d) = modeDiagonal (fun j => Real.sqrt (d j)) := by
  apply CFC.sqrt_unique
  · rw [modeDiagonal_mul]
    congr 1
    funext j
    exact Real.mul_self_sqrt (hd j)
  · exact (Matrix.PosSemidef.diagonal (fun i => Real.sqrt_nonneg (d i.1))).nonneg

/-- Thermal power covariance defined as `modeDiagonal (fun j => thermalQuadratureVariance (q j ^
a))`. -/
def thermalPowerCovariance {m : ℕ} (q : Fin m → ℝ) (a : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  modeDiagonal (fun j => thermalQuadratureVariance (q j ^ a))

theorem thermalPowerCovariance_posDef {m : ℕ} {q : Fin m → ℝ} {a : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (ha : 0 < a) :
    (thermalPowerCovariance q a).PosDef := by
  apply modeDiagonal_posDef
  intro j
  have h := half_le_thermalQuadratureVariance (Real.rpow_nonneg (hq₀ j) _)
    (Real.rpow_lt_one (hq₀ j) (hq₁ j) ha)
  linarith

/-- Thermal perturbation constant given by `1 + max 1 ((1 - τ) / τ)`. -/
def thermalPerturbationConstant (τ : ℝ) : ℝ := 1 + max 1 ((1 - τ) / τ)

/-- Thermal perturbation multiplier. -/
def thermalPerturbationMultiplier {m : ℕ} (q : Fin m → ℝ) (τ : ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  covariancePerturbationMultiplier (thermalPowerCovariance q (1 - τ))
    (thermalReferenceGap q τ) (thermalWoodburyFactor q τ)

/-- Thermal perturbation coefficient. -/
def thermalPerturbationCoefficient (q τ : ℝ) : ℝ :=
  (Real.sqrt (thermalQuadratureVariance (q ^ (1 - τ))))⁻¹ *
    (q ^ (-(τ / 2)) * (q ^ (-τ) - 1)⁻¹) *
      (Real.sqrt (thermalQuadratureVariance (q ^ τ) - thermalQuadratureVariance q))⁻¹

theorem thermal_reference_scalar_identity {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (thermalQuadratureVariance (q ^ τ) ^ 2 - 1 / 4) /
      (thermalQuadratureVariance (q ^ τ) - thermalQuadratureVariance q) =
        thermalQuadratureVariance (q ^ (1 - τ)) + thermalQuadratureVariance (q ^ τ) := by
  have h := thermalSandwich_covariance_appendixA hq₁ (Real.rpow_pos_of_pos hq₀ τ)
    (Real.rpow_lt_one hq₀.le hq₁ hτ₀) (thermal_parameter_lt_rpow hq₀ hq₁ hτ₁)
  have hquot : q / q ^ τ = q ^ (1 - τ) := by
    rw [Real.rpow_sub hq₀, Real.rpow_one]
  rw [hquot] at h
  linarith

theorem thermalPerturbationCoefficient_sq {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    thermalPerturbationCoefficient q τ ^ 2 =
      1 + thermalQuadratureVariance (q ^ τ) / thermalQuadratureVariance (q ^ (1 - τ)) := by
  have hv : 0 < thermalQuadratureVariance (q ^ (1 - τ)) := by
    have h := half_le_thermalQuadratureVariance (Real.rpow_nonneg hq₀.le _)
      (Real.rpow_lt_one hq₀.le hq₁ (sub_pos.mpr hτ₁))
    linarith
  have hH : 0 < thermalQuadratureVariance (q ^ τ) - thermalQuadratureVariance q :=
    sub_pos.mpr ((thermalQuadratureVariance_lt_iff hq₁
      (Real.rpow_lt_one hq₀.le hq₁ hτ₀)).mpr (thermal_parameter_lt_rpow hq₀ hq₁ hτ₁))
  have hL : (q ^ (-(τ / 2)) * (q ^ (-τ) - 1)⁻¹) ^ 2 =
      thermalQuadratureVariance (q ^ τ) ^ 2 - 1 / 4 := by
    have h := thermal_scalar_dilation_threshold hq₀ hq₁ hτ₀
    have hi := thermal_scalar_excess_inverse hq₀ hq₁ hτ₀
    calc
      _ = (q ^ (-(τ / 2)) * (q ^ (-τ) - 1)⁻¹ * q ^ (-(τ / 2))) *
          (q ^ (-τ) - 1)⁻¹ := by ring
      _ = _ := by rw [h, hi]; ring
  rw [thermalPerturbationCoefficient, mul_pow, mul_pow, inv_pow, inv_pow,
    Real.sq_sqrt hv.le, Real.sq_sqrt hH.le, hL]
  calc
    _ = (thermalQuadratureVariance (q ^ (1 - τ)))⁻¹ *
        ((thermalQuadratureVariance (q ^ τ) ^ 2 - 1 / 4) /
          (thermalQuadratureVariance (q ^ τ) - thermalQuadratureVariance q)) := by ring
    _ = _ := by
      rw [thermal_reference_scalar_identity hq₀ hq₁ hτ₀ hτ₁]
      field_simp [hv.ne']

theorem thermalPerturbationMultiplier_diagonal {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    thermalPerturbationMultiplier q τ =
      modeDiagonal (fun j => thermalPerturbationCoefficient (q j) τ) := by
  have hv (j : Fin m) : 0 < thermalQuadratureVariance (q j ^ (1 - τ)) := by
    have h := half_le_thermalQuadratureVariance (Real.rpow_nonneg (hq₀ j).le _)
      (Real.rpow_lt_one (hq₀ j).le (hq₁ j) (sub_pos.mpr hτ₁))
    linarith
  have hH (j : Fin m) : 0 < thermalQuadratureVariance (q j ^ τ) - thermalQuadratureVariance (q j) :=
    sub_pos.mpr ((thermalQuadratureVariance_lt_iff (hq₁ j)
      (Real.rpow_lt_one (hq₀ j).le (hq₁ j) hτ₀)).mpr
        (thermal_parameter_lt_rpow (hq₀ j) (hq₁ j) hτ₁))
  have hgap : thermalReferenceGap q τ =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ) - thermalQuadratureVariance
        (q j)) := by
    exact Matrix.diagonal_sub _ _
  rw [thermalPerturbationMultiplier, covariancePerturbationMultiplier,
    thermalPowerCovariance, hgap, modeDiagonal_sqrt (fun j => (hv j).le),
    modeDiagonal_sqrt (fun j => (hH j).le),
    modeDiagonal_inv (fun j => (Real.sqrt_pos.mpr (hv j)).ne'),
    modeDiagonal_inv (fun j => (Real.sqrt_pos.mpr (hH j)).ne'),
    thermalWoodburyFactor, modeDiagonal_mul, modeDiagonal_mul]
  rfl

theorem norm_sq_thermalPerturbationMultiplier_le {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    ‖thermalPerturbationMultiplier q τ‖ ^ 2 ≤ thermalPerturbationConstant τ := by
  have hk : 0 ≤ thermalPerturbationConstant τ := by
    unfold thermalPerturbationConstant
    linarith [le_max_left (1 : ℝ) ((1 - τ) / τ)]
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self,
    thermalPerturbationMultiplier_diagonal hq₀ hq₁ hτ₀ hτ₁,
    Matrix.conjTranspose_eq_transpose_of_trivial, transpose_modeDiagonal, modeDiagonal_mul]
  change ‖Matrix.diagonal (fun i : Fin m × Fin 2 =>
    thermalPerturbationCoefficient (q i.1) τ * thermalPerturbationCoefficient (q i.1) τ)‖ ≤ _
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hk).mpr
  intro i
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg _), ← pow_two,
    thermalPerturbationCoefficient_sq (hq₀ i.1) (hq₁ i.1) hτ₀ hτ₁]
  have hv : 0 < thermalQuadratureVariance (q i.1 ^ (1 - τ)) := by
    have h := half_le_thermalQuadratureVariance (Real.rpow_nonneg (hq₀ i.1).le _)
      (Real.rpow_lt_one (hq₀ i.1).le (hq₁ i.1) (sub_pos.mpr hτ₁))
    linarith
  have hcomp := thermalQuadratureVariance_power_comparison (hq₀ i.1).le (hq₁ i.1)
    hτ₀ (sub_pos.mpr hτ₁)
  have hratio := (div_le_iff₀ hv).mpr hcomp
  exact _root_.add_le_add_right hratio 1

end VacuumBellSeparation.Gaussian
