/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixGaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs

/-!
# The actual finite-dimensional matrix trace norm

The trace norm is trace |A|, where |A| is the genuine positive CFC square
root of AᵀA. Its orthogonal invariance is proved through positive square
root uniqueness and the ordinary matrix trace. No entrywise norm is
substituted for the manuscript's nuclear norm.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix trace norm. -/
def matrixTraceNorm (A : Matrix ι ι ℝ) : ℝ := (CFC.abs A).trace

theorem matrixTraceNorm_eq_sqrt_trace (A : Matrix ι ι ℝ) :
    matrixTraceNorm A = (CFC.sqrt (Aᵀ * A)).trace := by
  simp only [matrixTraceNorm, CFC.abs, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

theorem matrixTraceNorm_nonneg (A : Matrix ι ι ℝ) : 0 ≤ matrixTraceNorm A :=
  (CFC.abs_nonneg A).posSemidef.trace_nonneg

theorem matrixTraceNorm_eq_zero_iff (A : Matrix ι ι ℝ) : matrixTraceNorm A = 0 ↔ A = 0 := by
  rw [matrixTraceNorm, (CFC.abs_nonneg A).posSemidef.trace_eq_zero_iff, CFC.abs_eq_zero_iff]

theorem matrix_sqrt_orthogonal_conjugate
    (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1)
    {A : Matrix ι ι ℝ} (hA : 0 ≤ A) :
    CFC.sqrt (U * A * Uᵀ) = U * CFC.sqrt A * Uᵀ := by
  have hpos : 0 ≤ U * CFC.sqrt A * Uᵀ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      ((CFC.sqrt_nonneg A).posSemidef.mul_mul_conjTranspose_same U).nonneg
  apply CFC.sqrt_unique (hb := hpos)
  calc
    (U * CFC.sqrt A * Uᵀ) * (U * CFC.sqrt A * Uᵀ) =
        U * (CFC.sqrt A * (Uᵀ * U) * CFC.sqrt A) * Uᵀ := by noncomm_ring
    _ = U * A * Uᵀ := by
      rw [hU, Matrix.mul_one, CFC.sqrt_mul_sqrt_self A hA]

theorem matrix_abs_orthogonal_conjugate
    (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (A : Matrix ι ι ℝ) :
    CFC.abs (U * A * Uᵀ) = U * CFC.abs A * Uᵀ := by
  have hgram : (U * A * Uᵀ)ᵀ * (U * A * Uᵀ) = U * (Aᵀ * A) * Uᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = U * Aᵀ * (Uᵀ * U) * A * Uᵀ := by noncomm_ring
      _ = _ := by rw [hU, Matrix.mul_one]; noncomm_ring
  simp only [CFC.abs, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hgram, matrix_sqrt_orthogonal_conjugate U hU]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.posSemidef_conjTranspose_mul_self A).nonneg

theorem matrixTraceNorm_orthogonal_conjugate
    (U : Matrix ι ι ℝ) (hU : Uᵀ * U = 1) (A : Matrix ι ι ℝ) :
    matrixTraceNorm (U * A * Uᵀ) = matrixTraceNorm A := by
  rw [matrixTraceNorm, matrix_abs_orthogonal_conjugate U hU,
    Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  rfl

end VacuumBellSeparation.Gaussian
