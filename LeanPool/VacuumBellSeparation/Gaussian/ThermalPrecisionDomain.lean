/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixSandwichOrder
public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticBlocks
public import LeanPool.VacuumBellSeparation.Gaussian.QuadratureNormalization

/-!
# Literal thermal matrix precision and covariance domain

With faithful parameters `0<q_j<1` and τ>0, the real dilation has entries
`q_j^(-τ/2)` repeated in each quadrature. The actual precision matrix
`I-T²+T(V+I/2)⁻¹T` is positive definite exactly when the covariance lies
below the powered thermal covariance `diag(v(q_j^τ))`. This is the matrix
domain equivalence from Appendix A, without assuming a Gaussian trace or
a bounded extension of the inverse-domain form.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem modeDiagonal_posDef {d : ι → ℝ} (hd : ∀ i, 0 < d i) :
    (modeDiagonal d).PosDef := Matrix.PosDef.diagonal fun i => hd i.1

theorem modeDiagonal_inv {d : ι → ℝ} (hd : ∀ i, d i ≠ 0) :
    (modeDiagonal d)⁻¹ = modeDiagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [modeDiagonal_mul, ← modeDiagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hd i)

/-- Thermal quadrature dilation given by `modeDiagonal (fun i => q i ^ (-(τ / 2)))`. -/
def thermalQuadratureDilation (q : ι → ℝ) (τ : ℝ) : Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  modeDiagonal (fun i => q i ^ (-(τ / 2)))

/-- Thermal dilation excess given by `modeDiagonal (fun i => q i ^ (-τ) - 1)`. -/
def thermalDilationExcess (q : ι → ℝ) (τ : ℝ) : Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  modeDiagonal (fun i => q i ^ (-τ) - 1)

/-- Thermal coherent precision. -/
def thermalCoherentPrecision (q : ι → ℝ) (τ : ℝ)
    (V : Matrix (ι × Fin 2) (ι × Fin 2) ℝ) : Matrix (ι × Fin 2) (ι × Fin 2) ℝ :=
  1 - thermalQuadratureDilation q τ * thermalQuadratureDilation q τ +
    thermalQuadratureDilation q τ * (V + (1 / 2 : ℝ) • 1)⁻¹ * thermalQuadratureDilation q τ

omit [Fintype ι] in
theorem thermalQuadratureDilation_posDef {q : ι → ℝ}
    (hq₀ : ∀ i, 0 < q i) (τ : ℝ) : (thermalQuadratureDilation q τ).PosDef :=
  modeDiagonal_posDef fun i => Real.rpow_pos_of_pos (hq₀ i) _

omit [Fintype ι] in
theorem thermalDilationExcess_posDef {q : ι → ℝ} {τ : ℝ}
    (hq₀ : ∀ i, 0 < q i) (hq₁ : ∀ i, q i < 1) (hτ : 0 < τ) :
    (thermalDilationExcess q τ).PosDef :=
  modeDiagonal_posDef fun i => sub_pos.mpr
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hq₀ i) (hq₁ i) (neg_neg_of_pos hτ))

theorem thermalQuadratureDilation_sq {q : ι → ℝ} (hq₀ : ∀ i, 0 < q i) (τ : ℝ) :
    thermalQuadratureDilation q τ * thermalQuadratureDilation q τ - 1 =
      thermalDilationExcess q τ := by
  rw [thermalQuadratureDilation, modeDiagonal_mul]
  have heq (i : ι) : q i ^ (-(τ / 2)) * q i ^ (-(τ / 2)) = q i ^ (-τ) := by
    rw [← Real.rpow_add (hq₀ i)]
    congr 1
    ring
  simp_rw [heq]
  exact Matrix.diagonal_sub (fun i : ι × Fin 2 => q i.1 ^ (-τ)) (fun _ => 1)

theorem thermal_scalar_dilation_threshold {q τ : ℝ}
    (hq₀ : 0 < q) (hq₁ : q < 1) (hτ : 0 < τ) :
    q ^ (-(τ / 2)) * (q ^ (-τ) - 1)⁻¹ * q ^ (-(τ / 2)) =
      thermalQuadratureVariance (q ^ τ) + 1 / 2 := by
  have ht₀ := Real.rpow_pos_of_pos hq₀ τ
  have ht₁ := Real.rpow_lt_one hq₀.le hq₁ hτ
  have hden : (q ^ τ)⁻¹ - 1 ≠ 0 := ne_of_gt (sub_pos.mpr ((one_lt_inv₀ ht₀).mpr ht₁))
  have hsq : q ^ (-(τ / 2)) * q ^ (-(τ / 2)) = q ^ (-τ) := by
    rw [← Real.rpow_add hq₀]
    congr 1
    ring
  calc
    _ = q ^ (-τ) * (q ^ (-τ) - 1)⁻¹ := by rw [← hsq]; ring
    _ = thermalQuadratureVariance (q ^ τ) + 1 / 2 := by
      rw [Real.rpow_neg hq₀.le]
      unfold thermalQuadratureVariance
      field_simp [ht₀.ne', ne_of_gt (sub_pos.mpr ht₁), hden]
      ring

theorem thermalDilationExcess_inverse_congruence {q : ι → ℝ} {τ : ℝ}
    (hq₀ : ∀ i, 0 < q i) (hq₁ : ∀ i, q i < 1) (hτ : 0 < τ) :
    thermalQuadratureDilation q τ * (thermalDilationExcess q τ)⁻¹ *
      thermalQuadratureDilation q τ =
        modeDiagonal (fun i => thermalQuadratureVariance (q i ^ τ)) + (1 / 2 : ℝ) • 1 := by
  have hne (i : ι) : q i ^ (-τ) - 1 ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.one_lt_rpow_of_pos_of_lt_one_of_neg (hq₀ i) (hq₁ i) (neg_neg_of_pos hτ)))
  rw [thermalDilationExcess, modeDiagonal_inv hne, thermalQuadratureDilation,
    modeDiagonal_mul, modeDiagonal_mul]
  have heq (i : ι) : q i ^ (-(τ / 2)) * (q i ^ (-τ) - 1)⁻¹ * q i ^ (-(τ / 2)) =
      thermalQuadratureVariance (q i ^ τ) + 1 / 2 :=
    thermal_scalar_dilation_threshold (hq₀ i) (hq₁ i) hτ
  simp_rw [heq]
  exact (Matrix.diagonal_add (fun i : ι × Fin 2 => thermalQuadratureVariance (q i.1 ^ τ))
    (fun _ => (1 / 2 : ℝ))).symm.trans
      (congrArg (fun X => modeDiagonal (fun i => thermalQuadratureVariance (q i ^ τ)) + X)
        (Matrix.smul_one_eq_diagonal (1 / 2 : ℝ)).symm)

theorem thermalCoherentPrecision_posDef_iff {q : ι → ℝ} {τ : ℝ}
    (hq₀ : ∀ i, 0 < q i) (hq₁ : ∀ i, q i < 1) (hτ : 0 < τ)
    (V : Matrix (ι × Fin 2) (ι × Fin 2) ℝ)
    (hC : (V + (1 / 2 : ℝ) • 1).PosDef) :
    (thermalCoherentPrecision q τ V).PosDef ↔
      (modeDiagonal (fun i => thermalQuadratureVariance (q i ^ τ)) - V).PosDef := by
  have hP : thermalCoherentPrecision q τ V = sandwichPrecision
      (thermalDilationExcess q τ) (thermalQuadratureDilation q τ) (V + (1 / 2 : ℝ) • 1) := by
    rw [thermalCoherentPrecision, sandwichPrecision, ← thermalQuadratureDilation_sq hq₀]
    abel
  have hG : sandwichGap (thermalDilationExcess q τ) (thermalQuadratureDilation q τ)
      (V + (1 / 2 : ℝ) • 1) =
        modeDiagonal (fun i => thermalQuadratureVariance (q i ^ τ)) - V := by
    rw [sandwichGap, thermalDilationExcess_inverse_congruence hq₀ hq₁ hτ]
    abel
  rw [hP, sandwichPrecision_posDef_iff _ _ _
    (thermalDilationExcess_posDef hq₀ hq₁ hτ) (thermalQuadratureDilation_posDef hq₀ τ) hC, hG]

end VacuumBellSeparation.Gaussian
