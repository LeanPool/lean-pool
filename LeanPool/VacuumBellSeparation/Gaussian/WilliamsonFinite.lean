/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SkewOrthogonalCongruence

/-!
# Actual finite-dimensional Williamson factorization

For a positive definite real matrix `V` and a nonsingular real alternating
form `Ω`, form `B = (√V)⁻¹ Ω (√V)⁻¹`. The constructed orthogonal skew normal
form `B = O diag(λ) Ω_modes Oᵀ` gives `S = √V O diag(√λ)`. Direct matrix
identities prove `S Ω_modes Sᵀ = Ω` and `S diag(1/λ) Sᵀ = V`. A two-sided
inverse of `S` is constructed, including the zero-dimensional case.

The differing finite index types are explicitly equicardinal; the result
is a genuine invertible change of coordinates, not a rectangular dilation.
No Gaussian unitary implementation or uncertainty lower bound is asserted.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real finite-dimensional Williamson theorem, with an actual
invertible symplectic factor and strictly positive symplectic eigenvalues. -/
theorem exists_williamson_factorization (V Ω : Matrix ι ι ℝ)
    (hV : V.PosDef) (hΩ : Ωᵀ = -Ω) (hΩunit : IsUnit Ω) :
    ∃ (m : ℕ) (ν : Fin m → ℝ)
      (S : Matrix ι (Fin m × Fin 2) ℝ) (T : Matrix (Fin m × Fin 2) ι ℝ),
      Fintype.card ι = 2 * m ∧ (∀ i, 0 < ν i) ∧
      S * T = 1 ∧ T * S = 1 ∧
      S * (modeSymplecticForm (ι := Fin m)) * Sᵀ = Ω ∧ S * modeDiagonal ν * Sᵀ = V := by
  classical
  let C := CFC.sqrt V
  have hCpos : 0 ≤ C := CFC.sqrt_nonneg V
  have hCsym : Cᵀ = C := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hCpos.isSelfAdjoint.star_eq
  have hCC : C * C = V := by
    simpa only [pow_two] using CFC.sq_sqrt V hV.posSemidef.nonneg
  have hCunit : IsUnit C := (CFC.isUnit_sqrt_iff V hV.posSemidef.nonneg).mpr hV.isUnit
  have hCdet : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hCunit
  have hCCi : C * C⁻¹ = 1 := C.mul_nonsing_inv hCdet
  have hCiC : C⁻¹ * C = 1 := C.nonsing_inv_mul hCdet
  have hCiunit : IsUnit C⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hCunit
  let B := C⁻¹ * Ω * C⁻¹
  have hBskew : Bᵀ = -B := by
    simp only [B, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hCsym,
      hΩ, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hBunit : IsUnit B := (hCiunit.mul hΩunit).mul hCiunit
  have hundo : C * B * C = Ω := by
    simp only [B, ← Matrix.mul_assoc, hCCi, Matrix.one_mul]
    rw [Matrix.mul_assoc, hCiC, Matrix.mul_one]
  obtain ⟨m, μ, O, hμ, hOO, hOtO, hOB⟩ := exists_skew_orthogonal_congruence B hBskew hBunit
  let R := modeDiagonal (fun i => Real.sqrt (μ i))
  let Ri := modeDiagonal (fun i => (Real.sqrt (μ i))⁻¹)
  have hRRi : R * Ri = 1 := by
    dsimp only [R, Ri]
    rw [modeDiagonal_mul, ← modeDiagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (Real.sqrt_pos.mpr (hμ i)).ne'
  have hRiR : Ri * R = 1 := by
    dsimp only [R, Ri]
    rw [modeDiagonal_mul, ← modeDiagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hμ i)).ne'
  let S := C * O * R
  let T := Ri * Oᵀ * C⁻¹
  have hcard : Fintype.card ι = 2 * m := by
    have htr := Matrix.trace_mul_comm O Oᵀ
    rw [hOO, hOtO] at htr
    simp only [Matrix.trace_one, Fintype.card_prod, Fintype.card_fin] at htr
    norm_cast at htr
    omega
  refine ⟨m, (fun i => (μ i)⁻¹), S, T, hcard, (fun i => inv_pos.mpr (hμ i)),
    ?_, ?_, ?_, ?_⟩
  · calc
      S * T = C * (O * (R * Ri) * Oᵀ) * C⁻¹ := by
        simp only [S, T, Matrix.mul_assoc]
      _ = 1 := by rw [hRRi, Matrix.mul_one, hOO, Matrix.mul_one, hCCi]
  · calc
      T * S = Ri * (Oᵀ * (C⁻¹ * C) * O) * R := by
        simp only [S, T, Matrix.mul_assoc]
      _ = 1 := by rw [hCiC, Matrix.mul_one, hOtO, Matrix.mul_one, hRiR]
  · calc
      S * (modeSymplecticForm (ι := Fin m)) * Sᵀ =
          C * (O * (R * (modeSymplecticForm (ι := Fin m)) * R) * Oᵀ) * C := by
        simp only [S, R, Matrix.transpose_mul, transpose_modeDiagonal, hCsym,
          Matrix.mul_assoc]
      _ = C * (O * (modeDiagonal μ * (modeSymplecticForm (ι := Fin m))) * Oᵀ) * C := by
        rw [show R * (modeSymplecticForm (ι := Fin m)) * R = modeDiagonal μ *
          (modeSymplecticForm (ι := Fin m))
          from modeSqrt_symplectic_congruence μ (fun i => (hμ i).le)]
      _ = Ω := by rw [hOB, hundo]
  · calc
      S * modeDiagonal (fun i => (μ i)⁻¹) * Sᵀ =
          C * (O * (R * modeDiagonal (fun i => (μ i)⁻¹) * R) * Oᵀ) * C := by
        simp only [S, R, Matrix.transpose_mul, transpose_modeDiagonal, hCsym,
          Matrix.mul_assoc]
      _ = C * (O * Oᵀ) * C := by
        rw [show R * modeDiagonal (fun i => (μ i)⁻¹) * R = 1
          from modeSqrt_reciprocal_congruence μ hμ, Matrix.mul_one]
      _ = V := by rw [hOO, Matrix.mul_one, hCC]

end VacuumBellSeparation.Gaussian
