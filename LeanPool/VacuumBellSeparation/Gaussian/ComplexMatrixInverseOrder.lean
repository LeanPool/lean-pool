/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ComplexMatrixPositivity

/-!
# Strict inverse order for actual complex Hermitian matrices

The two actual Schur complements prove inverse order, and invertibility
upgrades it to strict positivity. This extends the real covariance lemma
to the literal complex quantum uncertainty matrices; no commutation is
assumed and zero-dimensional matrices remain covered.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem complex_matrix_inv_sub_inv_posSemidef_iff {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (A⁻¹ - B⁻¹).PosSemidef ↔ (B - A).PosSemidef := by
  let : Invertible B := hB.isUnit.invertible
  let : Invertible A⁻¹ := hA.inv.isUnit.invertible
  have h₁ := Matrix.PosDef.fromBlocks₁₁ (1 : Matrix n n ℂ) A⁻¹ hB
  have h₂ := Matrix.PosDef.fromBlocks₂₂ B (1 : Matrix n n ℂ) hA.inv
  have hi : (A⁻¹)⁻¹ = A :=
    A.nonsing_inv_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  simpa only [conjTranspose_one, one_mul, mul_one, hi] using h₁.symm.trans h₂

theorem complex_matrix_inv_difference_factorization {A B : Matrix n n ℂ}
    (hA : IsUnit A) (hB : IsUnit B) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  have hAi := A.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hBi := B.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  rw [mul_sub, sub_mul, mul_assoc, hBi, mul_one, hAi, one_mul]

theorem complex_matrix_difference_factorization {A B : Matrix n n ℂ}
    (hA : IsUnit A) (hB : IsUnit B) :
    B - A = A * (A⁻¹ - B⁻¹) * B := by
  have hAi := A.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hBi := B.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  rw [mul_sub, sub_mul, hAi, one_mul, mul_assoc, hBi, mul_one]

theorem complex_matrix_inv_sub_inv_isUnit_iff {A B : Matrix n n ℂ}
    (hA : IsUnit A) (hB : IsUnit B) :
    IsUnit (A⁻¹ - B⁻¹) ↔ IsUnit (B - A) := by
  constructor
  · intro h
    rw [complex_matrix_difference_factorization hA hB]
    exact (hA.mul h).mul hB
  · intro h
    rw [complex_matrix_inv_difference_factorization hA hB]
    exact ((Matrix.isUnit_nonsing_inv_iff.mpr hA).mul h).mul
      (Matrix.isUnit_nonsing_inv_iff.mpr hB)

/-- Actual positive-definite inverse order, including zero-dimensional
matrices, proved from the pinned positive-semidefinite Schur theorem. -/
theorem complex_matrix_inv_sub_inv_posDef_iff {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    (A⁻¹ - B⁻¹).PosDef ↔ (B - A).PosDef := by
  constructor
  · intro h
    have hs := (complex_matrix_inv_sub_inv_posSemidef_iff hA hB).mp h.posSemidef
    exact hs.posDef_iff_isUnit.mpr
      ((complex_matrix_inv_sub_inv_isUnit_iff hA.isUnit hB.isUnit).mp h.isUnit)
  · intro h
    have hs := (complex_matrix_inv_sub_inv_posSemidef_iff hA hB).mpr h.posSemidef
    exact hs.posDef_iff_isUnit.mpr
      ((complex_matrix_inv_sub_inv_isUnit_iff hA.isUnit hB.isUnit).mpr h.isUnit)


/-- A strict inverse-order criterion after an actual invertible Hermitian
congruence. The calibration is an explicit matrix equality, not a
commutation assumption on the variable D. -/
theorem complex_matrix_congruence_inverse_gap_iff
    {D C L A : Matrix n n ℂ} (hD : D.PosDef) (hC : C.PosDef)
    (hL : L.PosDef) (hcal : L * C⁻¹ * L = A) :
    (L * D⁻¹ * L - A).PosDef ↔ (C - D).PosDef := by
  have he : L * D⁻¹ * L - A = L * (D⁻¹ - C⁻¹) * star L := by
    rw [Matrix.star_eq_conjTranspose, hL.isHermitian.eq, ← hcal]
    noncomm_ring
  rw [he, hL.isUnit.posDef_star_right_conjugate_iff]
  exact complex_matrix_inv_sub_inv_posDef_iff hD hC

/-- Exact calibration from a square identity. Only the fixed matrices
C and L commute; the later covariance gap remains unrestricted. -/
theorem complex_matrix_inverse_calibration
    {C L A : Matrix n n ℂ} (hC : IsUnit C) (hcomm : C * L = L * C)
    (hsq : L * L = C * A) : L * C⁻¹ * L = A := by
  have hCi := C.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det C).mp hC)
  have hiC := C.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det C).mp hC)
  have he : C * (L * C⁻¹ * L) = C * A := by
    calc
      _ = (C * L) * C⁻¹ * L := by noncomm_ring
      _ = (L * C) * C⁻¹ * L := by rw [hcomm]
      _ = L * (C * C⁻¹) * L := by noncomm_ring
      _ = L * L := by rw [hiC, Matrix.mul_one]
      _ = _ := hsq
  have hh := congrArg (fun X => C⁻¹ * X) he
  simpa only [← Matrix.mul_assoc, hCi, Matrix.one_mul] using hh

end VacuumBellSeparation.Gaussian
