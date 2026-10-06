/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.SpectralBound
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# High-contrast homogenization: Setup.SpectralNorm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The scalar Loewner bound is the spectral norm

The reference text writes `|M|` for the spectral norm of a symmetric positive
semidefinite matrix, and the encoding used throughout is the scalar Loewner bound
`specBound M = inf {t ≥ 0 : M ≤ t I}`.  This file identifies the two: for a
positive semidefinite matrix, `specBound M` is the `ℓ²` operator norm of `M`,
that is, the norm carried by the identification of `Mat d` with the continuous
endomorphisms of `EuclideanSpace ℝ (Fin d)`.

One half is unconditional: Cauchy-Schwarz bounds the quadratic form of any matrix
by its operator norm times the squared length, so `specBound M ≤ ‖M‖` always.
The converse uses positive semidefiniteness through the square root: if
`0 ≤ M ≤ t I` then `M² ≤ t M` — because `t M - M² = M^{1/2}(t I - M)M^{1/2}` — and
therefore `‖M x‖² ≤ t² ‖x‖²`.
-/

namespace HCPolySupport
namespace HighContrast

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem matVecMul_smul_one₀ (t : ℝ) (x : Vec d) :
    matVecMul (t • (1 : Mat d)) x = t • x := by
  funext i
  simp [matVecMul, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]

private theorem vecDot_smul_self₀ (t : ℝ) (x : Vec d) :
    vecDot x (t • x) = t * vecNormSq x := by
  simp only [vecDot, vecNormSq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem le_of_sq_le_sq₀ {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := by
  have hsq := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_of_nonneg hv] at hsq
  exact le_trans (le_abs_self u) hsq

/-- A symmetric matrix moves across the Euclidean pairing. -/
private theorem vecDot_matVecMul_of_symm {R : Mat d} (hR : matTranspose R = R)
    (y w : Vec d) : vecDot y (matVecMul R w) = vecDot (matVecMul R y) w := by
  have h := vecDot_matVecMul_transpose y w R
  rwa [hR] at h

/-- A Hermitian real matrix is its own transpose in the ambient encoding. -/
private theorem matTranspose_of_isHermitian {R : Mat d} (hR : R.IsHermitian) :
    matTranspose R = R := by
  ext i j
  simpa [matTranspose, Matrix.IsHermitian, Matrix.conjTranspose_apply] using
    congrArg (fun N : Mat d => N i j) hR

/-- The Euclidean norm of a vector, squared, is its ambient squared length. -/
private theorem norm_toLp_sq (y : Vec d) :
    ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d))‖ ^ 2 = vecNormSq y := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The `ℓ²` operator norm controls the matrix-vector product. -/
private theorem vecNormSq_matVecMul_le (M : Mat d) (x : Vec d) :
    vecNormSq (matVecMul M x) ≤ ‖M‖ ^ 2 * vecNormSq x := by
  have hT : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M (WithLp.toLp 2 x)
      = WithLp.toLp 2 (matVecMul M x) := rfl
  have hle : ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ ≤
      ‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ := by
    rw [← hT]
    exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M).le_opNorm _
  have hsq : ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
      (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ :=
      norm_nonneg _
    calc ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ ^ 2
        = ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ *
            ‖(WithLp.toLp 2 (matVecMul M x) : EuclideanSpace ℝ (Fin d))‖ := sq _
      _ ≤ (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) *
            (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) :=
          mul_self_le_mul_self h0 hle
      _ = (‖M‖ * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖) ^ 2 := (sq _).symm
  rwa [norm_toLp_sq, mul_pow, norm_toLp_sq] at hsq

/-- **The scalar Loewner bound is at most the operator norm**, for every matrix:
Cauchy-Schwarz bounds the quadratic form of `M` by `‖M‖` times the squared
length. -/
theorem specBound_le_norm (M : Mat d) : specBound M ≤ ‖M‖ := by
  refine specBound_le (norm_nonneg M) ?_
  intro x
  rw [matVecMul_smul_one₀, vecDot_smul_self₀]
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq x (matVecMul M x)
  have hop := vecNormSq_matVecMul_le M x
  have hx := vecNormSq_nonneg x
  have hkey : vecDot x (matVecMul M x) ^ 2 ≤ (‖M‖ * vecNormSq x) ^ 2 := by
    calc vecDot x (matVecMul M x) ^ 2
        ≤ vecNormSq x * vecNormSq (matVecMul M x) := hcs
      _ ≤ vecNormSq x * (‖M‖ ^ 2 * vecNormSq x) := mul_le_mul_of_nonneg_left hop hx
      _ = (‖M‖ * vecNormSq x) ^ 2 := by ring
  have hfin := le_of_sq_le_sq₀ (mul_nonneg (norm_nonneg M) hx) hkey
  linarith only [hfin]

/-- **The operator norm is at most the scalar Loewner bound** on positive
semidefinite data.  If `0 ≤ M ≤ t I` then `M² ≤ t M ≤ t² I`, because
`t M - M² = M^{1/2}(t I - M)M^{1/2}`. -/
theorem norm_le_specBound {M : Mat d} (hM : M.PosSemidef) : ‖M‖ ≤ specBound M := by
  have ht : (0 : ℝ) ≤ specBound M := specBound_nonneg M
  have hL : MatLoewnerLE M (specBound M • (1 : Mat d)) :=
    matLoewnerLE_specBound_smul_one M
  have hq : ∀ y : Vec d, vecDot y (matVecMul M y) ≤ specBound M * vecNormSq y := by
    intro y
    have h := hL y
    rw [matVecMul_smul_one₀, vecDot_smul_self₀] at h
    linarith only [h]
  obtain ⟨hBpsd, hBB⟩ := matSqrt_spec hM
  set B : Mat d := matSqrt M with hBdef
  have hBT : matTranspose B = B := matTranspose_of_isHermitian hBpsd.isHermitian
  have hMT : matTranspose M = M := matTranspose_of_isHermitian hM.isHermitian
  have hMM : M * M = B * (M * B) := by
    rw [← hBB]
    simp [Matrix.mul_assoc]
  have hkey : ∀ y : Vec d,
      vecNormSq (matVecMul M y) ≤ specBound M ^ 2 * vecNormSq y := by
    intro y
    have hstep1 : vecNormSq (matVecMul B y) ≤ specBound M * vecNormSq y := by
      have hexp : vecNormSq (matVecMul B y) = vecDot y (matVecMul M y) := by
        simp only [vecNormSq]
        rw [← vecDot_matVecMul_of_symm hBT y (matVecMul B y), matVecMul_mul, hBB]
      rw [hexp]
      exact hq y
    have hexp2 : vecNormSq (matVecMul M y) =
        vecDot (matVecMul B y) (matVecMul M (matVecMul B y)) := by
      have e1 : vecNormSq (matVecMul M y) = vecDot y (matVecMul M (matVecMul M y)) := by
        simp only [vecNormSq]
        exact (vecDot_matVecMul_of_symm hMT y (matVecMul M y)).symm
      have e2 : matVecMul M (matVecMul M y) =
          matVecMul B (matVecMul M (matVecMul B y)) := by
        rw [matVecMul_mul, matVecMul_mul, matVecMul_mul, hMM, Matrix.mul_assoc]
      rw [e1, e2, vecDot_matVecMul_of_symm hBT]
    have hstep2 : vecNormSq (matVecMul M y) ≤
        specBound M * vecNormSq (matVecMul B y) := by
      rw [hexp2]
      exact hq (matVecMul B y)
    calc vecNormSq (matVecMul M y)
        ≤ specBound M * vecNormSq (matVecMul B y) := hstep2
      _ ≤ specBound M * (specBound M * vecNormSq y) :=
          mul_le_mul_of_nonneg_left hstep1 ht
      _ = specBound M ^ 2 * vecNormSq y := by ring
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ ht fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y : Vec d, x = WithLp.toLp 2 y := ⟨WithLp.ofLp x, rfl⟩
  have hxy : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) M (WithLp.toLp 2 y)
      = WithLp.toLp 2 (matVecMul M y) := rfl
  rw [hxy]
  refine le_of_sq_le_sq₀ (mul_nonneg ht (norm_nonneg _)) ?_
  rw [norm_toLp_sq, mul_pow, norm_toLp_sq]
  exact hkey y

/-- **`specBound` is the spectral norm.**  On positive semidefinite data the
scalar Loewner bound is exactly the `ℓ²` operator norm, so `specBound` is the
`|·|` of the reference text. -/
theorem specBound_eq_norm {M : Mat d} (hM : M.PosSemidef) : specBound M = ‖M‖ :=
  le_antisymm (specBound_le_norm M) (norm_le_specBound hM)

end

end HighContrast
end HCPolySupport
