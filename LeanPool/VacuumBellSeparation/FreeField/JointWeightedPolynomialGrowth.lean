/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.JointSymmetricPolynomialOperator
public import LeanPool.VacuumBellSeparation.FreeField.JointNormalizedMomentVectors

/-!
# Coefficient-sum nuclear bounds for the actual weighted polynomial

The monomial degree splits into the two spatial degrees exactly. Hence a
single exponential degree cost controls the full finite rank-one sum.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation

open Gaussian MvPolynomial
open scoped ENNReal

theorem spatialSixExponent_degree_sum (d : Fin 6 →₀ ℕ) :
    (∑ i, spatialSixLeftExponent d i) + (∑ i, spatialSixRightExponent d i) =
      d.sum (fun _ n => n) := by
  rw [d.sum_fintype (fun _ n => n) (fun _ => rfl), Fin.sum_univ_add (a := 3) (b := 3)]
  rfl

theorem nuclear_jointSymmetricPolynomialOperator_growth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (v : (Fin 3 → ℕ) → E) (P : MvPolynomial (Fin 6) ℂ)
    {A L : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L) {D : ℕ} (hD : P.totalDegree ≤ D)
    (hv : ∀ α, ‖v α‖ ≤ A * L ^ (∑ i, α i)) :
    operatorTraceNorm (jointSymmetricPolynomialOperator v P) ≤
      ENNReal.ofReal (2 * A ^ 2 * L ^ D * mvCoefficientNorm P) := by
  have hL₀ : 0 ≤ L := le_trans zero_le_one hL
  have hp (d : Fin 6 →₀ ℕ) (hd : d ∈ P.support) :
      ‖v (spatialSixLeftExponent d)‖ * ‖v (spatialSixRightExponent d)‖ ≤ A ^ 2 * L ^ D := by
    calc
      _ ≤ (A * L ^ (∑ i, spatialSixLeftExponent d i)) *
          (A * L ^ (∑ i, spatialSixRightExponent d i)) :=
        mul_le_mul (hv _) (hv _) (norm_nonneg _) (by positivity)
      _ = A ^ 2 * L ^ ((∑ i, spatialSixLeftExponent d i) +
          (∑ i, spatialSixRightExponent d i)) := by rw [pow_add]; ring
      _ ≤ A ^ 2 * L ^ D := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg A)
        apply pow_le_pow_right₀ hL
        rw [spatialSixExponent_degree_sum]
        exact (le_totalDegree hd).trans hD
  apply (nuclear_jointSymmetricPolynomialOperator_le v P).trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ 2 * ∑ d ∈ P.support, ‖P.coeff d‖ * (A ^ 2 * L ^ D) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum fun d hd => mul_le_mul_of_nonneg_left (hp d hd) (norm_nonneg _)
    _ = 2 * A ^ 2 * L ^ D * mvCoefficientNorm P := by
      rw [← Finset.sum_mul]
      unfold mvCoefficientNorm
      ring

end VacuumBellSeparation
