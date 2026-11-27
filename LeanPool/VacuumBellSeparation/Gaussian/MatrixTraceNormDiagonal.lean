/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.MatrixTraceNorm

/-!
# Diagonal estimates for the actual matrix trace norm

For a self-adjoint perturbation H, its absolute diagonal sum is bounded
by trace |H|. Bounded scalar weights therefore bound any diagonal trace
functional. This supplies the algebraic estimate used by the source
purity differential without assuming that differential formula.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι]

theorem matrix_abs_sub_nonneg {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    open scoped Classical in 0 ≤ CFC.abs A - A := by
  classical
  rw [CFC.abs_sub_self A hA.isSelfAdjoint, two_smul]
  exact add_nonneg (CFC.negPart_nonneg A) (CFC.negPart_nonneg A)

theorem matrix_abs_add_nonneg {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    open scoped Classical in 0 ≤ CFC.abs A + A := by
  classical
  rw [CFC.abs_add_self A hA.isSelfAdjoint, two_smul]
  exact add_nonneg (CFC.posPart_nonneg A) (CFC.posPart_nonneg A)

theorem abs_matrix_diagonal_le_abs_diagonal {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (i : ι) : open scoped Classical in |A i i| ≤ CFC.abs A i i := by
  classical
  have hm := (matrix_abs_sub_nonneg hA).posSemidef.diag_nonneg (i := i)
  have hp := (matrix_abs_add_nonneg hA).posSemidef.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, Matrix.add_apply] at hm hp
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable [DecidableEq ι]

theorem sum_abs_diagonal_le_matrixTraceNorm {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) : ∑ i, |A i i| ≤ matrixTraceNorm A := by
  change ∑ i, |A i i| ≤ ∑ i, CFC.abs A i i
  exact Finset.sum_le_sum fun i _ => abs_matrix_diagonal_le_abs_diagonal hA i

theorem abs_weighted_diagonal_le_matrixTraceNorm {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c) (w : ι → ℝ)
    (hw : ∀ i, |w i| ≤ c) :
    |∑ i, w i * A i i| ≤ c * matrixTraceNorm A := by
  calc
    |∑ i, w i * A i i| ≤ ∑ i, |w i * A i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, c * |A i i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hw i) (abs_nonneg _)
    _ = c * ∑ i, |A i i| := (Finset.mul_sum _ _ _).symm
    _ ≤ c * matrixTraceNorm A := mul_le_mul_of_nonneg_left
      (sum_abs_diagonal_le_matrixTraceNorm hA) hc

theorem matrix_abs_diagonal (d : ι → ℝ) :
    CFC.abs (Matrix.diagonal d) = Matrix.diagonal (fun i => |d i|) := by
  have hp : 0 ≤ Matrix.diagonal (fun i => |d i|) :=
    (Matrix.PosSemidef.diagonal (fun i => abs_nonneg (d i))).nonneg
  rw [CFC.abs]
  apply CFC.sqrt_unique (hb := hp)
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simpa only [pow_two] using sq_abs (d i)

theorem matrixTraceNorm_diagonal (d : ι → ℝ) :
    matrixTraceNorm (Matrix.diagonal d) = ∑ i, |d i| := by
  rw [matrixTraceNorm, matrix_abs_diagonal, Matrix.trace_diagonal]

end VacuumBellSeparation.Gaussian
