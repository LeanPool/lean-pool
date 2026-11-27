/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixTraceNormDiagonal

/-!
# Order bounds for the actual trace norm of a symmetric matrix

Spectral diagonalization identifies trace |A| with the sum of absolute
eigenvalues. If -B ≤ A ≤ B, positivity of both conjugated differences
bounds each eigenvalue by the corresponding diagonal entry of B. This
gives trace |A| ≤ trace B without an operator absolute-value monotonicity
claim (which would in general be false).
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrixTraceNorm_eq_sum_abs_eigenvalues {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) : matrixTraceNorm A = ∑ i, |hA.eigenvalues i| := by
  rw [matrixTraceNorm, CFC.abs_eq_cfc_norm A hA.isSelfAdjoint, hA.cfc_eq,
    Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq, Real.norm_eq_abs]

theorem matrixTraceNorm_le_trace_of_order_bounds
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hlo : -B ≤ A) (hhi : A ≤ B) :
    matrixTraceNorm A ≤ B.trace := by
  let U := (hA.eigenvectorUnitary : Matrix ι ι ℝ)
  have hdiag : Uᵀ * A * U = Matrix.diagonal hA.eigenvalues := by
    simpa only [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, Function.id_comp]
      using hA.conjStarAlgAut_star_eigenvectorUnitary
  have hleft : (Uᵀ * (B + A) * U).PosSemidef := by
    have hp : 0 ≤ B + A := by
      have := _root_.add_le_add_right hlo B
      simpa only [add_neg_cancel] using this
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hp.posSemidef.conjTranspose_mul_mul_same U
  have hright : (Uᵀ * (B - A) * U).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (sub_nonneg.mpr hhi).posSemidef.conjTranspose_mul_mul_same U
  have hbound : ∀ i, |hA.eigenvalues i| ≤ (Uᵀ * B * U) i i := by
    intro i
    have hl := hleft.diag_nonneg (i := i)
    have hr := hright.diag_nonneg (i := i)
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
      hdiag, Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_apply_eq] at hl hr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hUU : U * Uᵀ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, U] using
      Unitary.coe_mul_star_self hA.eigenvectorUnitary
  rw [matrixTraceNorm_eq_sum_abs_eigenvalues hA]
  calc
    ∑ i, |hA.eigenvalues i| ≤ (Uᵀ * B * U).trace := Finset.sum_le_sum fun i _ => hbound i
    _ = B.trace := by rw [Matrix.trace_mul_cycle, hUU, Matrix.one_mul]

theorem matrixTraceNorm_add_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    matrixTraceNorm (A + B) ≤ matrixTraceNorm A + matrixTraceNorm B := by
  have hupper : A + B ≤ CFC.abs A + CFC.abs B :=
    add_le_add (sub_nonneg.mp (matrix_abs_sub_nonneg hA))
      (sub_nonneg.mp (matrix_abs_sub_nonneg hB))
  have hlower : -(CFC.abs A + CFC.abs B) ≤ A + B := by
    have ha : -CFC.abs A ≤ A := by
      have h := matrix_abs_add_nonneg hA
      exact neg_le_iff_add_nonneg'.mpr h
    have hb : -CFC.abs B ≤ B := by
      have h := matrix_abs_add_nonneg hB
      exact neg_le_iff_add_nonneg'.mpr h
    simpa only [neg_add] using add_le_add ha hb
  have h := matrixTraceNorm_le_trace_of_order_bounds (hA.add hB) hlower hupper
  simpa only [Matrix.trace_add, matrixTraceNorm] using h

end VacuumBellSeparation.Gaussian
