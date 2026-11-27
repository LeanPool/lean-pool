/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixTraceNormOrder

/-!
# The actual trace-norm ideal bound for a symmetric sandwich

The positive trace estimate follows from BᵀB ≤ ‖B‖² I and the genuine
square root of the positive input. The symmetric case uses the proved
two-sided trace order bound, giving ‖B A Bᵀ‖₁ ≤ ‖B‖² ‖A‖₁. The norm of B
is the actual Euclidean operator norm selected by the matrix scope.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem trace_positive_sandwich_le_norm_sq
    {A : Matrix ι ι ℝ} (hA : 0 ≤ A) (B : Matrix ι ι ℝ) :
    (B * A * Bᵀ).trace ≤ ‖B‖ ^ 2 * A.trace := by
  let Q := CFC.sqrt A
  have hQ : 0 ≤ Q := CFC.sqrt_nonneg A
  have hQt : Qᵀ = Q := by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hQ.isSelfAdjoint.star_eq
  have hQQ : Q * Q = A := CFC.sqrt_mul_sqrt_self A hA
  have hbound : Bᵀ * B ≤ ‖B‖ ^ 2 • (1 : Matrix ι ι ℝ) := by
    rcases isEmpty_or_nonempty ι with hi | hi
    · let := hi
      exact le_of_eq (Subsingleton.elim _ _)
    · let := hi
      have hs : IsSelfAdjoint (Bᴴ * B) := IsSelfAdjoint.star_mul_self B
      have hb : Bᴴ * B ≤ algebraMap ℝ (Matrix ι ι ℝ) ‖Bᴴ * B‖ :=
        le_algebraMap_of_spectrum_le (ha := hs) fun x hx =>
          (Real.le_norm_self x).trans (spectrum.norm_le_norm_of_mem hx)
      rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hb
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
        Algebra.algebraMap_eq_smul_one, pow_two] using hb
  have hp : 0 ≤ Q * (‖B‖ ^ 2 • (1 : Matrix ι ι ℝ) - Bᵀ * B) * Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, hQt] using
      ((sub_nonneg.mpr hbound).posSemidef.mul_mul_conjTranspose_same Q).nonneg
  have he : Q * (‖B‖ ^ 2 • (1 : Matrix ι ι ℝ) - Bᵀ * B) * Q =
      ‖B‖ ^ 2 • A - Q * (Bᵀ * B) * Q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hQQ]
  have ht : (B * A * Bᵀ).trace = (Q * (Bᵀ * B) * Q).trace := by
    rw [← hQQ]
    calc
      _ = ((B * Q) * (Q * Bᵀ)).trace := congrArg Matrix.trace (by noncomm_ring)
      _ = ((Q * Bᵀ) * (B * Q)).trace := Matrix.trace_mul_comm _ _
      _ = _ := congrArg Matrix.trace (by noncomm_ring)
  have htr := hp.posSemidef.trace_nonneg
  rw [he, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul] at htr
  rw [ht]
  linarith

theorem matrixTraceNorm_sandwich_le
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (B : Matrix ι ι ℝ) :
    matrixTraceNorm (B * A * Bᵀ) ≤ ‖B‖ ^ 2 * matrixTraceNorm A := by
  have hBA : (B * A * Bᵀ).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose B hA
  have hupper : B * A * Bᵀ ≤ B * CFC.abs A * Bᵀ := by
    apply sub_nonneg.mp
    have h := (matrix_abs_sub_nonneg hA).posSemidef.mul_mul_conjTranspose_same B
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_sub, Matrix.sub_mul] using h.nonneg
  have hlower : -(B * CFC.abs A * Bᵀ) ≤ B * A * Bᵀ := by
    apply neg_le_iff_add_nonneg'.mpr
    have h := (matrix_abs_add_nonneg hA).posSemidef.mul_mul_conjTranspose_same B
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_add, Matrix.add_mul] using h.nonneg
  exact (matrixTraceNorm_le_trace_of_order_bounds hBA hlower hupper).trans
    (trace_positive_sandwich_le_norm_sq (CFC.abs_nonneg A) B)

end VacuumBellSeparation.Gaussian
