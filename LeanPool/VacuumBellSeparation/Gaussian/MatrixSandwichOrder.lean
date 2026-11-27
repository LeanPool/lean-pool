/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SandwichAlgebra
import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-!
# Positive matrix domain of the inverse Gaussian sandwich

The two Schur complements of the same actual block matrix prove inverse
order reversal. Invertibility of the two differences upgrades the result
to positive definiteness. Congruence then proves the Appendix A precision
criterion without a commutativity assumption on the covariance matrix.
No operator sandwich or Gaussian trace formula is assumed here.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem matrix_inv_sub_inv_posSemidef_iff {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (A⁻¹ - B⁻¹).PosSemidef ↔ (B - A).PosSemidef := by
  let : Invertible B := hB.isUnit.invertible
  let : Invertible A⁻¹ := hA.inv.isUnit.invertible
  have h₁ := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix n n ℝ) A⁻¹ hB
  have h₂ := Matrix.PosDef.fromBlocks₂₂ B (1 : Matrix n n ℝ) hA.inv
  have hi : (A⁻¹)⁻¹ = A :=
    A.nonsing_inv_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  simpa only [conjTranspose_one, one_mul, mul_one, hi] using h₁.symm.trans h₂

theorem matrix_inv_difference_factorization {A B : Matrix n n ℝ}
    (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  have hAi := A.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hBi := B.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  rw [mul_sub, sub_mul, mul_assoc, hBi, mul_one, hAi, one_mul]

theorem matrix_difference_factorization {A B : Matrix n n ℝ}
    (hA : IsUnit A) (hB : IsUnit B) :
    B - A = A * (A⁻¹ - B⁻¹) * B := by
  have hAi := A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hBi := B.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  rw [mul_sub, sub_mul, hAi, one_mul, mul_assoc, hBi, mul_one]

theorem matrix_inv_sub_inv_isUnit_iff {A B : Matrix n n ℝ}
    (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (A⁻¹ - B⁻¹) ↔ IsUnit (B - A) := by
  constructor
  · intro h
    rw [matrix_difference_factorization hA hB]
    exact (hA.mul h).mul hB
  · intro h
    rw [matrix_inv_difference_factorization hA hB]
    exact ((Matrix.isUnit_nonsing_inv_iff.mpr hA).mul h).mul
      (Matrix.isUnit_nonsing_inv_iff.mpr hB)

/-- Actual positive-definite inverse order, including zero-dimensional
matrices, proved from the pinned positive-semidefinite Schur theorem. -/
theorem matrix_inv_sub_inv_posDef_iff {A B : Matrix n n ℝ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (A⁻¹ - B⁻¹).PosDef ↔ (B - A).PosDef := by
  constructor
  · intro h
    have hs := (matrix_inv_sub_inv_posSemidef_iff hA hB).mp h.posSemidef
    exact hs.posDef_iff_isUnit.mpr
      ((matrix_inv_sub_inv_isUnit_iff hA.isUnit hB.isUnit).mp h.isUnit)
  · intro h
    have hs := (matrix_inv_sub_inv_posSemidef_iff hA hB).mpr h.posSemidef
    exact hs.posDef_iff_isUnit.mpr
      ((matrix_inv_sub_inv_isUnit_iff hA.isUnit hB.isUnit).mpr h.isUnit)

/-- The actual precision is positive definite exactly on the positive
covariance gap. `S=T²-I` is the later thermal specialization. -/
theorem sandwichPrecision_posDef_iff (S T C : Matrix n n ℝ)
    (hS : S.PosDef) (hT : T.PosDef) (hC : C.PosDef) :
    (sandwichPrecision S T C).PosDef ↔ (sandwichGap S T C).PosDef := by
  let B := T * S⁻¹ * T
  have hB : B.PosDef := by
    simpa only [hT.isHermitian.eq] using
      hS.inv.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hT.isUnit)
  have hTi := T.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
  have hiT := T.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det T).mp hT.isUnit)
  have hBi : B⁻¹ = T⁻¹ * S * T⁻¹ := by
    simp only [B, Matrix.mul_inv_rev,
      S.nonsing_inv_nonsing_inv ((Matrix.isUnit_iff_isUnit_det S).mp hS.isUnit), mul_assoc]
  have hconj : sandwichPrecision S T C = T * (C⁻¹ - B⁻¹) * star T := by
    rw [Matrix.star_eq_conjTranspose, hT.isHermitian.eq, hBi]
    calc
      sandwichPrecision S T C = T * C⁻¹ * T - S := by
        unfold sandwichPrecision
        abel
      _ = T * C⁻¹ * T - (T * T⁻¹) * S * (T⁻¹ * T) := by rw [hTi, hiT, one_mul, mul_one]
      _ = T * (C⁻¹ - (T⁻¹ * S * T⁻¹)) * T := by noncomm_ring
  rw [hconj, hT.isUnit.posDef_star_right_conjugate_iff]
  exact matrix_inv_sub_inv_posDef_iff hC hB

end VacuumBellSeparation.Gaussian
